# Reference-app comparison: Cambra vs. an off-the-shelf stack

## Why this exists

Cambra's seed pitch deck claims the language collapses a stack that teams
otherwise assemble from many systems. We have latency evidence for that claim
and no code-volume evidence, because **no published study measures
lines-of-code by purpose for modern service architectures** — we looked hard,
including two 2026 repo-mining papers, and the number does not exist.

So we are going to measure it ourselves: build the *same application* twice —
once in Cambra, once on a conventional stack — and count.

The output feeds a slide. That means the comparison has to survive a hostile
reading by a technical investor. **A rigged comparison is worth less than no
comparison.** See "Fairness rules" below; they are the most important part of
this brief.

## The application: the storefront north-star, augmented

The north star lives at `tests/programs/storefront/` (`v0.cambra`, `v1.cambra`,
`mod.rs`). Read it first. In ~120 lines it covers transactional inventory
under concurrent handlers, three HTTP endpoints, a streaming feed of committed
order lines, a revenue rollup pinned to transaction time, and compile-time
verification (refinement types plus a `static assert` that lifts to a
postcondition).

**What it lacks, and what you are adding: durable execution, and an
ETL-to-warehouse path.**

### Step 1 — design the durable-execution augmentation

Research which storefront use cases genuinely need durable execution, i.e.
multi-step processes that must survive process restarts, need retries with
backoff, need compensation when a later step fails, or need timers measured in
hours or days. A cart-and-checkout saga is the obvious candidate — reserve
inventory, charge payment, create fulfilment, send confirmation, with
compensation if payment fails after reservation — and cart-abandonment timers
are a second, since a 24-hour wait is impossible without durable state. Look
for others; pick what makes the strongest, most realistic example. Do not
invent a use case that exists only to make Cambra look good.

Write the design down before implementing.

## What to build

### A. The Cambra version

Extend the north star to cover the augmented feature set. Best effort — **the
language is early and will not support all of this.** Mutability, loops with
loop-carried state, and `groupby` are currently blocked at lowering; see
`docs/demo-programs.md` and `docs/plan.md`.  <!-- doc-refs-ignore: docs/plan.md is not in this repo -->

Where Cambra cannot express something, **write what the program should look
like and mark the gap precisely**: what construct is missing, what it would
take, and whether it is a syntax gap, a lowering gap, or a genuine semantic
hole. This gap list is a first-class deliverable — arguably more valuable to
the team than the line count. Follow the repo's `docs/demo-programs.md`
conventions for blocked programs.

Be explicit in the report about what runs and what does not. Do not present
aspirational code as working.

### B. The conventional version

The same features on an off-the-shelf stack, with one component per layer:

| Layer | Local | Should translate to |
|---|---|---|
| Serving | your choice (FastAPI, Litestar, ...) | same |
| Transactional DB | Postgres in Docker | same |
| Durable execution | Temporal (dev server) | Temporal Cloud |
| Message bus | Redpanda or NATS | Kafka |
| ETL | your choice, keep it conventional | same |
| Warehouse | DuckDB | Snowflake / BigQuery |
| Object storage | local filesystem | S3 |

**It must actually run locally, end to end, with a single command** — a
`docker compose up` plus a make target, or equivalent. Write integration tests
that exercise the real flows: place an order, hit the stats endpoint, run a
checkout that fails at payment and verify compensation, fire an abandonment
timer with a compressed clock.

The substitutions must be *swaps, not simplifications*: DuckDB stands in for
Snowflake, but the ETL should still be a real pipeline; local disk stands in
for S3, but through an interface that a real object store would satisfy.
Anywhere you simplify in a way that would not survive production, say so in
the report.

## Fairness rules — read twice

1. **Same features, both sides.** If Cambra cannot do something, that is a gap
   to report, not a feature to drop from the conventional side.
2. **Write the conventional version the way a good engineer would.** Idiomatic,
   reasonably factored, no gratuitous boilerplate, no deliberately verbose
   style. Use the frameworks' own conveniences. If a sensible engineer would
   reach for a library, reach for it.
3. **Count generated code separately** — protobuf/OpenAPI stubs, ORM models,
   migrations produced by a tool. It is real code that has to exist and be
   maintained, but a reader will discount it, so it must be its own line.
4. **Count config as config.** YAML, Helm, compose files, Temporal worker
   registration, topic definitions, dbt project files, Dockerfiles.
5. **No cherry-picking.** Report the total honestly even where it is
   unflattering.

## The measurement — the actual deliverable

Count both implementations by **purpose**, not by file. Categories, which you
may refine but should not quietly narrow:

- domain / business logic
- serialization, DTOs, API request-response plumbing
- connection and pool management
- database schema and migrations
- fault tolerance: retries, timeouts, circuit breakers, compensation
- flow control and backpressure
- authorization and policy
- ETL and data movement
- observability instrumentation: logging, metrics, tracing, dashboards
- configuration and infrastructure-as-code
- tests, split into unit versus integration/contract/e2e
- generated code

Use a mechanical counter (`cloc`, `tokei`, or `scc`) for file-level totals, and
a documented manual classification for purpose. **Write down the counting
methodology and commit the script**, so the number is reproducible and a
skeptic can rerun it. State clearly which lines were classified by hand.

## Deliverables

1. The augmented Cambra program(s), following repo conventions, with the gap
   list.
2. The working conventional implementation, with its run instructions and
   passing integration tests.
3. `REPORT.md`: the design, the two implementations, the LoC table by purpose,
   the methodology, the gap list, and an explicit "what this comparison does
   and does not show" section. Write that last section as though a skeptical
   investor wrote it.
4. A PR.

## Where things go

Put the conventional implementation under `reference-app/` at the repo root,
clearly marked as not part of the Rust build and excluded from `ci.sh`. Keep
Cambra sources under `tests/programs/` per existing convention. Put `REPORT.md`
in `docs/`.

## Ground rules

- Read `CLAUDE.md` first. It governs. Note especially "when in doubt, ask" —
  but the person who commissioned this is away, so prefer documenting a
  decision and its alternatives in the report over blocking on it.
- `./ci.sh` must pass before the PR. Nothing you add should slow or break it.
- Commit incrementally with real messages. This is a large task; do not
  accumulate one enormous diff.
- See `docs/git_spice_cheatsheet.md` for the PR workflow.  <!-- doc-refs-ignore: docs/git_spice_cheatsheet.md is not in this repo; the repo uses jj -->
- Do not modify the deck or anything outside this repo.

## The one thing to get right

The number this produces will be put in front of investors. Its value is
entirely in being defensible. If the honest answer is that the gap is 3x rather
than 30x, that is a fine and useful result — report it plainly. If the Cambra
side cannot be written at all yet, that is also a real result: say so, and
report the gap list as the finding.
