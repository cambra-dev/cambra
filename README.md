# Cambra

Cambra is a programming language for building data-intensive applications — transaction processing, streaming, analytics, serving — as **one coherent program** rather than a stack of separately-modeled components. The premise (argued at length in [Composition Shouldn't be this Hard](https://cambra.dev/blog/announcement/)) is that systems turn brittle when their components interact through a model lower than the one they're written in: tooling loses its leverage at exactly the boundaries where the hard bugs live. Cambra collapses those boundaries — one language, one type system, one execution model, whole-program tooling.

The audience for that leverage now includes machines. Cambra treats **coding agents as first-class programmers**: an agent converges on a correct system only as fast as the feedback it gets, and Cambra's job is to maximize the quality of that feedback. Two loops organize the design:

- **Verification — does the program provably satisfy its invariants?** The type system is built on refinement types: types carry semantic predicates (`{q: Int | q >= 0}`), and because the whole application lives in one model, those predicates can compose across what would otherwise be component boundaries. The core machinery — refinement inference, constraint solving, explicit refinement acquisition — is in the CCL type system today; whole-application contracts on top of it are the driving design direction.
- **Validation — does the program do what its author intended?** The runtime primitive is **program branching**: a candidate version branches off the running application — logic and state together, not just the code or the data — gets exercised under a realistic workload, and has its behavior compared against production before anything ships. The language is designed from the ground up to make this tractable: the surface syntax lowers to a referentially-transparent intermediate representation, so different versions of programs can be compared syntactically with well-defined semantics.
 
These features are landing incrementally; the [demo program library](docs/demo-programs.md) tracks exactly what runs today.

## Status: research preview

This repository is published so the approach can be read, studied, and discussed — **not** because Cambra is ready to use.

- **No releases, no binaries.** If you want to poke at it, build from source (below).
- **Everything is unstable.** The Pythonic surface syntax is itself transitional — CHL is converging toward its own syntax (see the spec's *Direction* notes). Core language, types, and interfaces all change without notice.
- **Not for production.** The interpreter is a single-node runtime under active development; substantial parts of the language are decided but not yet implemented. [docs/demo-programs.md](docs/demo-programs.md) is an honest ledger of what runs today and what doesn't.
- **Closed contribution, open discussion.** We aren't accepting pull requests at this stage, but issues — bug reports, questions, design discussion — are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md).

## How it works

- **Denotationally**, a Cambra program is a term in a pure, dependently-typed functional language.
- **Operationally**, a Cambra program compiles to a dataflow **operator** implementing a producer/consumer interface, and the runtime drives the resulting operator graph with streaming dataflow semantics. Pipelining, incremental computation, parallelization, and vectorization are properties of the execution model, not features bolted onto it.

Programs are written in a Pythonic surface syntax — the Cambra High-level Language (**CHL**) — that lowers into a small core language (**CCL**: literals, records, lambdas, lets, application), where the program is type-checked, optimized, and converted to operators.

The aim is to abstract over memory, threads, and connections the way garbage collection abstracted over allocation: the programmer writes the logic and the high-level architecture; batching, incrementality, join strategies, and scheduling are the runtime's job. Put differently: the elegance that query planners bring to `SELECT` statements, applied to whole programs.

```python
products = [
    {sku: "espresso", price: 3},
    {sku: "latte",    price: 5},
]

# Orders arrive over HTTP: each POST body is an order record.
orders, order_acks = http_serve("8080", "POST", "/order")
for o in orders:
    order_acks << "ok\n"

# Rolling revenue, served: the order stream joined to the catalog,
# summed up to each reading transaction's time.
revenue_reqs, revenue_resps = http_serve("8080", "GET", "/revenue")
for req in revenue_reqs:
    with txn = begin():
        so_far = orders.restrict(lambda o: o.time < txn.current_time())
        revenue = sum([p.price * o.qty for p in products for o in so_far if p.sku == o.sku])
        revenue_resps[req.id] = str(revenue) + "\n"
```

The comprehension is not an embedded query DSL, and `orders` is not a list — it's the stream of requests hitting `/order`. The planner notices the equality predicate and lowers the cross product to a keyed hash-join. And note what `/revenue` returns: a bare `sum` over the order stream would denote *total* revenue — a value that exists only once the stream closes — so the handler instead pins the aggregate to its transaction's time, making "revenue to date" a well-defined read at any moment. The pinned view is materializable: the runtime is free to maintain the join-and-sum incrementally as orders arrive rather than rescanning the feed per request.

The ingest half of this program runs today, and so does the batch form of the query — swap the endpoint for an order list and the join-plus-`sum` runs end to end (`["> " + line for line in stdin()]` is likewise a complete streaming program). The `/revenue` handler is written in the decided-but-still-landing part of the language — transactional reads over feeds with time-pinned aggregates; the [program ledger](docs/demo-programs.md) pins this exact shape (`txn_kv`) and tracks its blockers. The direction ([spec](docs/chl-spec.md)) is the full storefront this example is trimmed from: concurrent handlers over transactional state, promotion budgets as time-pinned views just like this one, and invariants like non-negative inventory discharged by the refinement type system (deleting the guard that maintains them is a type error) — decided and specified, not yet running.

## Reading map

Ordered for a newcomer; each layer is precise about what is implemented versus decided versus tentative.

1. [docs/design.md](docs/design.md) — the guided tour: the language feature by feature, the compilation pipeline, and the execution model — with explicit markers for what runs today versus decided direction.
2. [docs/chl-spec.md](docs/chl-spec.md) — the surface-language specification. Status markers separate implemented behaviour from decided-but-unimplemented direction.
3. [docs/operational-semantics/summary.md](docs/operational-semantics/summary.md) — the runtime's formal model: **tilings** (progress algebras of monotonically-growing partial results), **guards** (structural decomposition of a computation), and **operators** (the producer/consumer counterpart of a function). Full definitions in [semantics.md](docs/operational-semantics/semantics.md), a worked end-to-end example in [example.md](docs/operational-semantics/example.md).
4. [docs/demo-programs.md](docs/demo-programs.md) — runnable programs mapped to their status: what works, what's blocked, and on what.
5. [src/design.md](src/design.md) — source layout and the index of per-module design docs.

## Building from source

Requires a recent Rust toolchain (pinned in [rust-toolchain.toml](rust-toolchain.toml)).

```bash
cargo build          # build
cargo test           # run tests
./ci.sh              # full CI suite (fmt + clippy in debug & release + doc + tests)
```

Run a program:

```bash
cargo run -- tests/programs/filter_and_aggregate/program.cambra
```

### Web inspector

Pass `--inspect` to serve a live dashboard showing the parsed CHL AST, the lowered CCL, the operator graph, and runtime producer state:

```bash
cargo run -- --inspect tests/programs/inner_join/program.cambra
```

The inspector defaults to port 8080 (`--inspect=9090` to change it). After the program finishes, the process stays alive so you can browse `http://localhost:<port>`; Ctrl+C to exit.

### Control port

Pass `--control` to let a running program be diffed against, and replaced by, a new version of its source. Both endpoints take the new source as the query string or the request body:

```bash
cargo run -- --control tests/programs/http_greeter/program.cambra

# in another terminal, with the edited program in v2.cambra:
curl --data-binary @v2.cambra localhost:8081/diff
curl --data-binary @v2.cambra localhost:8081/update
```

`/diff` reports how the two versions differ and changes nothing. `/update` replaces the program in place: sockets stay open, and every binding whose computation is unchanged keeps running with what it has accumulated. An edit to a mutating loop rebuilds that loop's store, and the entries it had are re-derived from the requests its source still holds. Add `stage=<name>&` before the source to diff somewhere other than the default (`lowered`, `inferred`, `inlined`, `channelized`, `lambda-elim`, `planned`).

An update may only change the logic between the sources and sinks the program already has; a version that opens a new one is rejected and the running program is left serving. See [live-update.md](src/ccl/design/live-update.md).

The control port defaults to 8081 (`--control=9090` to change it).

## License

Apache 2.0 — see [LICENSE](LICENSE).
