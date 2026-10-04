# Diagnostics

How an inference diagnostic writes the types it reports.

---

## How a diagnostic writes a type

An annotation mismatch writes both types in CHL with `chl_print::chl_type`: the annotation as
written, and the inferred type as the annotation that would state it. Every other diagnostic writes
types with `Display for Type`.

A collection is written as the collection type it is
([chl-spec.md, "6.3 Direction: collection types [Decided]"](../../../docs/chl-spec.md#63-direction-collection-types-decided)),
over its domain. The last column says whether the written form, used as an annotation, lowers back to
the same type. `Box`, `Source`, a dependent `FullMap` and an index range written as a refinement have
no annotation syntax. A predicate is written as the comprehension or membership test a reader would
write, which lowers to a different term than the one the checker holds.

| Inferred | Written | Lowers back |
| --- | --- | --- |
| a list literal, or a comprehension over one | `Array(3, Int)` | yes |
| a filtered comprehension | `FullMap({UInt where _ < 3 and xs[_] > 1}, Int)` | no |
| a map or set literal | `FullMap({String where _ in ["a", "b"]}, Int)` | no |
| `groupby(xs, key)` | `FullMap(k: {Bool where _ in [key(x) for x in xs]}, FullMap({UInt where _ < 3 and key(xs[_]) == k}, Int))` | no |
| a `List`, `Map`, `Set` or `Collection` | `List(Int)`, `Map(String, Int)`, … | yes |
| `box(a) if c else box(b)` | `Box(Array(2, Int) \| Array(3, Int))` | no |
| `stdin()` | `Source(stdin, String)` | no |
| a feed | `Feed(Int)` | no |

- **A collection over an index range is an `Array`.** A collection over any other domain is a
  `FullMap` over that domain, written as a type. An index range alone is `{UInt where _ < 𝑛}`,
  the bound an array's index carries
  ([chl-spec.md, "3.9 Subscript and attribute access"](../../../docs/chl-spec.md#39-subscript-and-attribute-access)).
- **A key the value depends on is named.** `FullMap(k: 𝐾, 𝑉)` is a `FullMap` whose value type
  mentions its key `k`, as a group-by's groups do. A function whose result type mentions its
  parameter is `(x: 𝑇) => 𝑈`.
- **A sum over named alternatives is a `Box`** of each alternative, as `box` built it
  ([chl-spec.md, "7.5 `box`"](../../../docs/chl-spec.md#75-box)).
- **A refinement is written with `where`**, its predicate in CHL. A literal's type is its
  singleton, `{Int where _ == 5}`. Two refinements of one type are two `where`s, since a refinement
  holding `p and q` is a different refinement from the two.
- **What CHL cannot write is marked, never dropped.** A part with no CHL spelling is written with
  `Display for Type` between `‹…›`.

`a_written_type_prints_as_an_annotation_that_lowers_back` (`ccl/chl_print.rs`) checks the rows
marked "yes", and `tests/compilation_pipeline/chl_types.rs` checks each row end to end.
