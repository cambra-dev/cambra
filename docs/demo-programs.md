# Demo Programs

A status table mapping each demo program in
[`tests/programs/`](../tests/programs/) to whether it currently works.

Each row maps a program to its current status and, when blocked, to the
feature that must land for it to become `working`.  Each program is its own subdirectory
containing a `program.cambra` source plus a `mod.rs` with one or more
`#[test]` functions — when a blocked program starts succeeding (or a working
one starts failing), the test goes red and prompts an update.

## Running a program manually

Every program in the table below is a runnable `.cambra` file (named
`program.cambra`, except `storefront`, which has `v0.cambra` and `v1.cambra`
— the two sides of its version upgrade).  To run one by hand:

```bash
cargo run -- tests/programs/<name>/program.cambra
```

To open the live web inspector while it runs (shows the parsed CHL AST,
the lowered CCL, the operator graph, and runtime producer state):

```bash
cargo run -- --inspect tests/programs/<name>/program.cambra
```

Two programs need a small substitution before they'll run as-is:

- **`http_greeter`** uses `{PORT}` as a placeholder so the integration test
  can pick a free TCP port.  Swap it for a literal (e.g. `8080`) before
  running manually:

  ```bash
  sed 's/{PORT}/8080/g' tests/programs/http_greeter/program.cambra > /tmp/greet.cambra
  cargo run -- /tmp/greet.cambra
  # then in another terminal:
  curl localhost:8080/greet
  ```

- **`streaming_echo`** reads from stdin — pipe input:

  ```bash
  printf "hello\nworld\n" | cargo run -- tests/programs/streaming_echo/program.cambra
  ```

The `🚧 blocked` programs in the table will panic or be rejected at
lowering when run manually — that's the point.
See [Known issues](#known-issues-surfaced-by-these-programs) for details on what's blocking each.

## Adding to this table

When you add a program under [`tests/programs/`](../tests/programs/), add a
row here.  See [tests/programs/main.rs](../tests/programs/main.rs) for the
list of registered programs and [tests/programs/common/mod.rs](../tests/programs/common/mod.rs)
for the helpers each `mod.rs` uses (`expect_scalar`,
`expect_compile_error`, `expect_scalar_currently_buggy`, plus the
HTTP-sink and subprocess utilities).

## North-star programs and corpus policy

The gallery's north-star is [`storefront`](../tests/programs/storefront/) —
one operational application spanning transactions, streaming, analytics,
and serving, in two versions (`v0.cambra`, `v1.cambra`) whose diff is a
version upgrade.  Corpus policy: the storefront is **not** staged into
progressive versions-as-tests.  Each capability it needs is isolated by a
small feature-focused satellite program that pins that gap alone
(`discount_contract`, `nonneg_inventory`, `ledger_balance`, alongside the
earlier north-stars `txn_kv`, `reachability`, and `fanout`).  The
satellites keep failures legible — one gap, one red test — while the
storefront keeps the composition honest: features that pass in isolation
must also pass composed, and its single test goes red at each layer of
unblocking to prompt the next pin.  Its
[`mod.rs`](../tests/programs/storefront/mod.rs) documents the orchestration
plan and the full dependency map.

## Programs

| Program | Use case | Exercises | Status | Notes / Blocker |
| --- | --- | --- | --- | --- |
| [arithmetic](../tests/programs/arithmetic/) | Chain two bindings | `let`, binops | ✅ working | Smoke-test for sequencing and reference resolution. |
| [prefix_lines](../tests/programs/prefix_lines/) | Transform a list of strings | list comprehension, string concat | ✅ working | The canonical streaming-pipeline shape; precursor to a real stdin/echo program. |
| [filter_and_aggregate](../tests/programs/filter_and_aggregate/) | "SELECT SUM(score) FROM users WHERE age >= 18" | record literal, field access, comp filter on let-bound source, `sum` | ✅ working | Returns `253`. Exercises a comp filter on a let-bound source — the filter must survive lowering through planning (it rides a `Cast` node on the refined domain). |
| [generator_pipeline](../tests/programs/generator_pipeline/) | Compose two generators (filter then square), then `max` | `def` + `yield`, generator composition, aggregate | ✅ working | Demonstrates UDF call sites being inlined and fused through to operator conversion. |
| [groupby_rollup](../tests/programs/groupby_rollup/) | Group sales records by region and total per region | `groupby` over records, `lambda`, inner projection, `sum` | 🚧 blocked | Operator conversion panics on the inner-projecting comprehension (`curry` combinator unsupported). See [known issues](#known-issues-surfaced-by-these-programs). |
| [inner_join](../tests/programs/inner_join/) | INNER JOIN of users × orders on user-id | hash-join (`if x.id == y.fk`), record fields, multi-source comp | ✅ working | The lowering planner sees the equality filter and lowers to a keyed lookup. |
| [http_greeter](../tests/programs/http_greeter/) | Three HTTP endpoints sharing a `prefix` let | `http_serve`, `<<` feed, deferred output, multi-route on one port | ✅ working (sink) | Real HTTP roundtrip — test fires three requests on a background thread while the main thread drives the scheduler. Source uses `{PORT}` placeholder. |
| [streaming_echo](../tests/programs/streaming_echo/) | Prefix each stdin line with "> " | `stdin()` source, list comprehension | ✅ working | Tested via subprocess so the real OS stdin file descriptor is exercised; substring-matched against captured stdout. |
| [for_accumulator](../tests/programs/for_accumulator/) | Fold via mutable accumulator | for-loop with loop-carried state | ✅ working | Loop-body reassignment of a pre-loop binding is lowered to a CCL `Loop` accumulator slot. |
| [while_counter](../tests/programs/while_counter/) | Count up with a while loop | `while`, mutability | 🚧 blocked | While-loop lowering is not yet implemented. Currently rejected at lowering. |
| [reachability](../tests/programs/reachability/) | Transitive closure (recursive query) | self-referential binding, `Set(T)` dedup-by-type, `++`, hash-join in a cycle | 🚧 blocked | North-star recursive query. Parse-blocked on record-term syntax `(src=1, dst=2)`; then `Set(T)` + the self-referential (recursive) binding. |
| [fanout](../tests/programs/fanout/) | Polymorphic sink constructor (fan-out pipe head) | `Feed(_)` type, `<<` feed, annotation-only forward decl, element polymorphism | 🚧 blocked | `Feed(_)` annotation unsupported; the forward declaration doesn't parse. Not Unix `tee` — returns the writable *head*. |
| [txn_kv](../tests/programs/txn_kv/) | Transactional KV store over HTTP + a stream-aggregate `/stats` endpoint | `requires Transaction`, `with begin()`, `abort()`, `Mut(..., Txn)`, atomic read-modify-write, `Option` lookup, `match`, `\` lambdas/`restrict`/`count`, structured requests | 🚧 blocked | Lexer rejects the `` ` `` on the `` `some ``/`` `none `` variant tags, the first of a stack of blockers. Subsumes the former standalone `kv_store` (concurrent handlers share state → must be transactional) and `hit_counter` (the request-stream aggregate). |
| [discount_contract](../tests/programs/discount_contract/) | Function contract via boundary asserts | `assert` preconditions + postcondition, lift to CCL refinements, call-site discharge | 🚧 blocked | The CHL contract surface (see [the function-contracts Direction note](chl-spec.md#6-types-informal-sketch)). Parse-blocked on `assert`; behind it, the lift itself. Expected `75` once working. |
| [nonneg_inventory](../tests/programs/nonneg_inventory/) | Stock reservation against a refined store | `Mut(Map(String, {Int where _ >= 0}), Txn)` value refinement, map literal `[k -> v]`, guarded decrement discharging it, `match`/`Option` | 🚧 blocked | The storefront's oversell invariant in isolation — deleting the guard must be a type error. Lex-blocked on the `` ` `` variant tag; behind it, the `->` map entry in the store literal. |
| [ledger_balance](../tests/programs/ledger_balance/) | Deposit ledger + time-pinned `/balance` view | feed written inside transactions, transaction time on feed elements, `restrict(\e -> e.time < txn.current_time())`, `sum` | 🚧 blocked | Lifts `txn_kv`'s `/stats` idiom from request streams to feeds — `e.time` comes from the feed's transaction-time domain, not the feeder. Lex-blocked on the `\` lambda. |
| [storefront](../tests/programs/storefront/) | **North-star app**: transactional orders + inventory + contract-checked pricing + time-indexed revenue views, in V0 and V1 | everything the four rows above pin, plus type aliases (`Dollars`/`Qty`/`ItemPricing`/`SKU`), record refinements, a value-dependent key type, `FullMap` total lookups, `static assert`, HTTP-lib validation derived from handler types, `groupby` rollup iterated as `key -> g` entry pairs, map comprehension `[k -> v for …]`, status-code response constructors (`http.ok`/`http.not_found`/`http.conflict`, via `import http`), map-valued `/stats` response, version upgrade | 🚧 blocked | Two sources (`v0.cambra`, `v1.cambra` — the diff is the budgeted-flash-sale upgrade) under one orchestrating test; its `mod.rs` documents the full dependency list. See [the corpus policy above](#north-star-programs-and-corpus-policy). Lex-blocked on the `` ` `` variant tag. |

## Known issues surfaced by these programs

Each entry below corresponds to a program in the table that's deliberately
written in its natural shape, which exposes a bug.  The test for the program
pins the current broken behavior; once the bug is fixed, the test goes red
and prompts the author to switch to `expect_scalar` with the correct answer.

### Records-shaped groupby panics at operator conversion

[Reproduced by: `groupby_rollup`](../tests/programs/groupby_rollup/)

`[sum([s.amount for s in g]) for g in groupby(sales, lambda r: r.region)]`
panics with `"Only higher-order combinators (map, const, zip) can take an
input operator; found input for non-combinator curry"`.  Blocked on
completing `curry` combinator support in `operator_conversion`.

Expected output once unblocked:
`Function [ "east" -> 200, "south" -> 75, "west" -> 300 ]`.

## Future-batch wishlist

Programs we want eventually but haven't written yet — these are good seeds for
when you go to add more.

- **Two-input join over HTTP** — register two `http_serve` endpoints, join
  their inputs by a shared key, return the combined response.  Needs:
  multi-way join planning (in progress) and a way to express the join over
  deferred collections.
- **Pipeline of HTTP fetches** — fan out to N URLs, join on result.  Needs:
  HTTP *client* source (not just server).
- **Real-time leaderboard** — sliding-window aggregate over an HTTP-fed stream.
  Needs: time-windowed aggregates and incremental sum.
- **Deep nested-loop perf demo** — triple-nested for-comprehension over
  large literal lists (replacement for the deleted `examples/slow.cambra`).
  Measures how cross-product compilation scales; ideally paired with a
  benchmark harness.
- **Version upgrade** — the first instance now exists: `storefront` carries
  `v0.cambra`/`v1.cambra` as two files whose diff is the upgrade, exercising
  version dispatch over persistent transactional state at the `t_new` branch
  point.  Still open: the `Versioned` node shape and dispatch semantics (no
  isolating feature program yet), and long-term a v2 of *every* program (a
  diffing dimension across the corpus); branch/merge is out of scope for now.
