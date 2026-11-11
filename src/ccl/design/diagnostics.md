# Diagnostics

How an inference diagnostic writes the types it reports, and the source positions it labels.

---

## What a message names

A message names what failed by its role in the program, and its span says where.

- **A mismatch names the role of the failing value.** `Type mismatch for {role}` reads
  `this call`, `this argument`, `the matched value`, `a write in the transaction`, or the operator
  `` `+` ``, never the name of a node or the expression written in CCL.
- **A trait failure names the operator or function**: ``No Addable instance for `+` ``, or
  `Iterable::elements` for a function a construct calls.
- **No message about the program prints an expression.** `ScopeViolation` and the consistency
  check (`infer/check.rs`) report compiler bugs and print CCL. The error's node is its location
  (`LocatedInferError::node_id`), which `compile_program` resolves to a span.

---

## How a diagnostic writes a type

A diagnostic writes every type in CHL with `chl_print::chl_type`. An annotation mismatch writes
the annotation as written, a bounded one as `<: T`, and the inferred type as the annotation that
would state it. A report of a compiler bug, such as `InferError::ScopeViolation` or a type that
survived a pass that erases it, writes `Display for Type`: its reader is the compiler's
developer.

`chl_print::renders_alike` compares the text a diagnostic writes, including descriptions that
hide structural differences. A mismatch whose sides read alike reports the hidden difference;
a data-domain mismatch instead reports the sub-comparison that rejected it. Neither use decides
type equality.

A family applied at a binder the compiler minted, outside the family that binds it, is written at
the spelling an unnamed binder of the text would take: `V(k)`.

A collection is written as the collection type it is
([chl-spec.md, "6.3 Direction: collection types [Decided]"](../../../docs/chl-spec.md#63-direction-collection-types-decided)),
over its domain. The last column says whether the written form, used as an annotation, lowers back
to the same type. `Box`, `Source`, a dependent data function `(k: 𝐾) |=> 𝑉` and an index range
written as a refinement have no annotation syntax. A predicate is written as the comprehension or
membership test a reader would write, which lowers to a different term than the one the checker
holds.

| Inferred | Written | Lowers back |
| --- | --- | --- |
| a list literal, or a comprehension over one | `Array(3, Int)` | yes |
| a filtered comprehension | `{UInt where _ < 3 and xs[_]! > 1} \|=> Int` | no |
| a map or set literal | `{String where _ in ["a", "b"]} \|=> Int` | no |
| `groupby(xs, key)` | `(k: {Bool where _ in [key(x) for x in xs]}) \|=> {UInt where _ < 3 and key(xs[_]!) == k} \|=> Int` | no |
| a `List`, `Map`, `Set` or `Collection` | `List(Int)`, `Map(String, Int)`, … | yes |
| `box(a) if c else box(b)` | `Box(Array(2, Int) \| Array(3, Int))` | no |
| `stdin()` | `Source(stdin, String)` | no |
| a feed | `Feed(Int)` | no |
| a nominal type's family argument | `\k: Bool -> {UInt where _ < 3 and key(xs[_]) == k} \|=> Int`, or `T` where the body reads no binder | no |

- **A collection over an index range is an `Array`.** A collection over any other domain is a
  data-function type `𝐷 |=> 𝑉` over that domain. An index range alone is `{UInt where _ < 𝑛}`,
  the bound an array's index carries
  ([chl-spec.md, "3.9 Subscript and attribute access"](../../../docs/chl-spec.md#39-subscript-and-attribute-access)).
- **A key the value depends on is named.** `(k: 𝐾) |=> 𝑉` is a data function whose value type
  mentions its key `k`, as a group-by's groups do. A function whose result type mentions its
  parameter is `(x: 𝑇) => 𝑈`. A binder the compiler minted is spelled `k` (a key) or `x` (a
  parameter or a comprehension's variable), numbered where another name in the type already reads
  as that. A family a nominal type takes, `Type::Family`, is written `\k: 𝐾 -> 𝑇`, and as `𝑇`
  where `𝑇` reads no binder, which is the constant family the annotation `𝑇` lowers to.
- **A read of a collection is a proven lookup, `xs[_]!`; any other application is a call, `f(x)`.**
  The two differ only in the function's kind, so the types inside a predicate are resolved when the
  error is raised (`coalesce_for_error`), while their variables still hold their bounds. An
  application of a function whose type names no kind is `‹not printable yet›`.
- **A sum over named alternatives is a `Box`** of each alternative, as `box` built it
  ([chl-spec.md, "7.4 `box`"](../../../docs/chl-spec.md#74-box)).
- **A refinement is written with `where`**, its predicate in CHL. A literal's type is its
  singleton, `{Int where _ == 5}`. Two refinements of one type are two `where`s, since a refinement
  holding `p and q` is a different refinement from the two.
- **A point-free predicate is read at its argument.** `λ` elimination writes `_ == 1` as
  `__elem ▷ ((id, 1 ▷ const) ▷ zip ≫ eq)`, and `Printer::point` reads the combinators back to
  `_ == 1`. `nand`, `nor` and `xnor` are written as negations, `not (p and q)`, and
  `int_eq_uint((x, _))`, which relates an `Int` and a `UInt`, as `x == _`.
- **A `def`'s parameter is written by its name.** A `def` of several parameters binds them as
  one tuple (`uncurry_params` in `lower/functions.rs`), whose binder records the parameters'
  spellings (`Name::positions`), so `__arg_tuple_0.0` is written `a`.
- **What CHL cannot write is described, never dropped and never spelled with a name the program
  did not write.**

  | Part | Written |
  | --- | --- |
  | an inference variable, numbered within the message so its occurrences read as one type (`chl_print::Writer`) | `‹?1›` |
  | a reference to a function parameter or collection key bound outside the written type | `‹outer argument›` |
  | a sum's witness read inside the sum's values | `‹outer keys›` |
  | the witness projected through a value `c` | `‹the keys of c›` |
  | a dependent tuple's read of an earlier component | `‹position 0›`, inside the tuple `{𝐴, 𝐵}` |
  | a demand admitting arms it does not list | ``{`a{Int} \| ‹more arms›}`` |
  | anything else: a channel domain, a positional variant, a sum of several witnesses | `‹not printable yet›` |

  The solver's binder for an application's expected function (`SyntheticKind::SolverArg`) is
  written `‹outer argument›` too: a type reading it is that function's result.

`a_written_type_prints_as_an_annotation_that_lowers_back` (`ccl/chl_print.rs`) checks the rows
marked "yes", and `tests/it/compilation_pipeline/chl_types.rs` checks the first table's rows
end to end.

---

## Secondary labels

An error is reported at the node whose rule drew the failing edge, and each other position the
edge involves is a secondary label (`LocatedInferError::related`): `x = id((sku=1))` then
`x.at` is reported at `x.at`, with "the value comes from here" at `id((sku=1))`.

- **Origins on bounds.** `Bound::origin` records where a bound's bounding side came from: for a
  lower bound, the expression the value came from; for an upper bound, what demanded it. An
  `Origin` is a node, or the span of a bound or requirement written in a `Poly`
  (`PolyParam::bound_at`, `TraitRequirement::at`), which has no node. A span is no part of a
  type's identity: equality and hashing of those two types leave it out.
- **The walk carries them.** `ConstrainCache` holds the origins of the edge being walked, set by
  its caller (`ConstrainCache::at`): emission sets the node under emission, and a
  specialization's pin sets the use. Recording a bound stores its bounding side's origin, and
  closing an edge over a stored bound walks on with that bound's origin on its side. Freshening
  and extrusion copy origins, so a definition's bounds point into its body at every use. The
  first edge to fail records its two origins (`ConstrainCache::take_failure`).
- **Trait obligations.** An obligation demands from where it was stated
  (`TraitObligation::required_at`): its operator, or the requirement it was instantiated from. A
  failed narrowing records the obligation as the demand and the contribution's origin as the
  value.
- **Written demands.** The `Var` arm checks a parameter's bound and instantiates a requirement
  under `Typing::with_demand_at`, so a failure points at the bound or the requirement as written.
- **Rendering.** `compile_program` resolves a node through the lowering projection and keeps a
  label whose span lies outside the primary span, reading "required here" or "the value comes
  from here".

Not covered:

- A concrete type carries no origin, so a value meeting a demand without passing through an
  inference variable has no value label: `x = (sku=1)` then `x.at`
  (`a_concrete_value_meeting_a_demand_directly_has_no_label`).
- An obligation does not record which contribution narrowed its candidates, so a conflict between
  two operands labels only the later operand's source: `a = id("s")`, `b = id(1)`, then `a + b`
  labels `id(1)` and not `id("s")`.
- An error raised at coalesce, such as an incompatible join or a use whose instantiation does not
  resolve, has no edge and so no label. The exception is an error a specialization raises that is
  the use's
  ([type-inference.md, "Checking a definition alone"](type-inference.md#checking-a-definition-alone)):
  it is reported at the use, labelled "required here" where the body failed.
- The inspector's diagnostic carries one span (`inspector_model::wire::Diagnostic`), so it shows
  no secondary label.
