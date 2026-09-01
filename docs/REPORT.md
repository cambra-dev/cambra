# Reference-app comparison: Cambra vs. an off-the-shelf stack

The storefront north-star, built twice — once in Cambra, once on a conventional stack — and counted
by purpose. The application is the north star
([`tests/programs/storefront/`](../tests/programs/storefront/)) augmented with durable execution and
an ETL-to-warehouse path.

The number is for a slide, so it has to survive a hostile reading. Everything that would flatter
Cambra without being true is called out where it occurs, and
[section 8](#8-what-this-comparison-does-and-does-not-show) is written from the skeptic's side.
Read it before quoting anything above it.

## 1. Summary

**Application code: 207 lines of Cambra against 1,385 lines on the conventional stack — 6.7×.**
Tests and local stand-ins excluded from both sides; every line of both implementations counted and
classified by a committed script.

Three qualifications belong in the same breath as that number.

**The Cambra program does not compile.** Not one of its 207 lines executes today: `v2.cambra` is
rejected at lexing, one line into `quote`. The conventional implementation runs, and its 17
end-to-end tests pass against eight live services. This is a comparison of a written program against
a working system, and no amount of care in the counting changes that.

**Business logic barely shrinks.** Domain code is 92 lines against 131 — 1.4×. Everything else
around it is 115 lines against 1,254 — 10.9×. Cambra's claim is not that the business rules get
shorter; it is that most of what surrounds them disappears. A reader who expected the first claim
should stop here.

**The ratio is sensitive to what you count.** Including the end-to-end tests on both sides, on the
argument that Cambra needs the same ones and needs no unit tests, gives 4.1×. Taking the
`config-infra` row at face value — Cambra 3, conventional 320 — requires believing that a deployed
Cambra program needs no image, no process supervision, and no environment configuration; charging it
a plausible 30 to 60 lines for those gives 5.8× to 5.2×, and 3.8× to 3.5× with the tests as well.

The honest headline is a range, **roughly 3.5× to 6.7×** depending on those two decisions, and the
shape of the saving matters more than its size: it falls almost entirely outside the domain logic,
in serialization (18×), connection management (23×), data movement (21×), and the machinery of
moving state between systems that do not share a type system.

## 2. Design

### 2.1 Which storefront use cases need durable execution

A use case needs durable execution when it is a multi-step process that must survive process
restarts, retry with backoff, compensate a completed step when a later one fails, or wait on a timer
measured in hours or days. Six storefront candidates were assessed against those four criteria.

| Use case | Multi-step | Retry | Compensation | Long timer | Verdict |
|---|---|---|---|---|---|
| Checkout saga: reserve → authorize → fulfil → confirm | yes | yes | yes | no | **Built** |
| Cart abandonment: remind at 24h, release soft holds at 72h | no | no | no | yes | **Built** |
| Authorize-now, capture-at-ship (auth expires in ~7 days) | yes | yes | yes | yes | Assessed, not built |
| Returns: RMA → receive → inspect → refund, 30-day window | yes | yes | no | yes | Assessed, not built |
| Backorder: wait for restock, then notify and auto-order | yes | no | no | yes | Assessed, not built |
| Order intake (`/order`), restock (`/restock`) | no | no | no | no | **Excluded** |

The two built cases are the ones that isolate the criteria cleanly. The checkout saga is
multi-step with compensation and per-step retry and no timer; cart abandonment is a timer with
cancellation and nothing else. Between them they cover all four criteria, and neither is a
construction that exists only to make Cambra look good — the saga is the canonical durable-execution
example in the vendor literature, and a cart-abandonment timer is standard commerce practice.

The three assessed-not-built cases are compositions of the same primitives over longer horizons.
Authorize-now/capture-at-ship is the saga with a week-long timer inside it; returns are the saga
with a 30-day timer; backorder is a wait on an external event with a timeout. Building them would
add duration to both sides without adding a mechanism to either, so they are named here and left
out. The report's line counts therefore understate both implementations equally.

Order intake and restock are excluded on the other side of the line: they are single ACID
transactions against one database. Routing them through a workflow engine is a mistake a reader
should not have to discount for. They stay as they are in the north star.

### 2.2 The feature set, identical on both sides

Fairness rule 1 is that both sides carry the same features. This is that list.

**Operational** — from the north star, unchanged.

1. `POST /order` — reserve stock, price the line, record it. `409` on oversell, `404` on unknown
   SKU, `422` on a negative quantity.
2. `POST /restock` — atomic increment.
3. `GET /stats` — revenue per SKU from a snapshot-consistent read.
4. Budgeted flash sale — half off list price while cumulative discount spend is under budget, with
   a per-item cost floor. The budget is read inside the ordering transaction, so two concurrent
   orders cannot both spend the last of it.
5. Two invariants: stock never goes negative, and no line ever sells below cost.

**Durable execution** — new.

6. `POST /checkout` — start the saga. Reserve inventory, authorize payment against an external
   payment service, create a fulfilment, send a confirmation. Each external step retries with
   exponential backoff. A failure after reservation compensates: void the authorization, release
   the reservation.
7. `GET /checkout/{id}` — saga status.
8. `POST /carts` — a cart with an abandonment deadline. Checking out cancels it; firing it marks
   the cart abandoned and emits the event a reminder campaign reads. A cart holds no inventory, on
   both sides, so nothing is reserved and nothing needs releasing.

**ETL to warehouse** — new.

9. Committed order lines leave the transactional database through an outbox and onto a topic.
10. A stream consumer batches the topic into Parquet objects in object storage, partitioned by day.
11. A loader ingests new objects into the warehouse; a transform builds a `daily_sku_revenue` mart.
12. `GET /analytics/daily-revenue` — served from the warehouse, not from the operational store.

**Cross-cutting** — structured logs, metrics, tracing; configuration; migrations; unit and
integration tests.

### 2.3 Cambra design

The augmentation needs two primitives that do not exist in CHL today. Everything else the feature
set requires is either already in the language or already on its
[decided-but-unimplemented list](chl-spec.md#12-reserved-for-future-work).

Both primitives are the same shape as something CHL already has, which is why they are two and not
six.

#### A keyed external call is the dual of `http.serve`

`http.serve(port, method, path)` returns `(requests, responses)`: an incoming collection and a
deferred outgoing one, paired by request. An outbound call is that pair reversed — an outgoing
collection of requests and an incoming collection of results, paired by a key the program supplies:

```python
charges, charge_results = http.call("payments", "POST", "/charges")

charges << (key=checkout_id, amount=total)     # dispatch
...
match charge_results[checkout_id]:             # consume, whenever it lands
    case `ok(receipt): ...
    case `failed(reason): ...
```

The key is the idempotency key, and the durability contract is stated on it: **for each key the
runtime dispatches at most one call and records its result durably before any consumer observes
it.** A restart mid-call re-dispatches only if no result was recorded. That contract is what a
workflow engine sells; here it is a property of one source.

The apparent cycle — a feed of this program causes a source of this program — is well-founded for
the same reason every other cycle in CCL is: the result at key `k` depends only on the request at
`k`, which is strictly earlier. It is the causal-accessor argument from
[src/ccl/design/mutability.md](../src/ccl/design/mutability.md) with the key in place of the time
position.

#### A deadline is a source over transactional state

A timer is not a new kind of clock; it is an obligation the runtime takes on from a map of
deadlines:

```python
deadlines: Mut(Map(CartId, Time), Txn) := []
due = clock.due(deadlines)      # one element per key whose deadline has passed
```

Scheduling is a write, rescheduling is a write, and cancelling is a delete — all ordinary
transactional mutation, so cancellation needs no separate surface and cannot race the fire. The
source is the runtime's promise to deliver an event when the state says one is owed, which is the
watermark advancing over a domain that the mutability substrate already maintains.

#### What falls out without new surface

- **Retry with backoff** is a failed result writing a new deadline and re-dispatching under a new
  attempt key. It needs no loop, so it does not wait on `while` lowering. The retry construct a
  workflow SDK supplies as a configuration object is two writes here.
- **Compensation** is an ordinary transaction that the saga's state machine reaches. What durable
  execution adds is not the compensating step but the guarantee it runs, and that guarantee is the
  durability of the saga state — a `Mut(Map(K, V), Txn)` — plus the at-most-once call contract
  above.
- **The saga itself** is a per-key state machine over transactional state, advanced by one `for`
  loop per event source. No orchestration construct appears.

Once state durability is a substrate property and external calls carry an at-most-once contract,
durable execution has nothing irreducible left. Cambra's state durability is **[Sketched]**, not
implemented ([design.md](design.md)), so that is a claim about the model rather than about a running
system.

#### ETL

The mart is a view over the `orders` feed in the same program, so steps 9–11 of the feature set have
no counterpart on the Cambra side at all. Step 12 is a rollup keyed by day.

The archive to object storage does have a counterpart and Cambra cannot write it: there is no
object-storage sink, and `Time` has no arithmetic to bucket by day with. Retention and cold storage
are real requirements that an in-program view does not meet, so this is a gap and not a saving.

The saving on steps 9–11 is architectural, not syntactic: the conventional side needs a pipeline
because analytics lives in a different system, and Cambra's position is that it need not. A reader
should discount it exactly as far as they disagree with that position, and
[section 8](#8-what-this-comparison-does-and-does-not-show) makes the case against it.

#### Programs

`tests/programs/storefront/v2.cambra` carries the augmented application; the diff from `v1.cambra`
is the augmentation, matching the corpus policy in
[demo-programs.md](demo-programs.md#north-star-programs-and-corpus-policy). Four satellite programs
pin the new gaps one at a time, so each failure stays legible:

| Satellite | Pins |
|---|---|
| `external_call` | the keyed outbound call and its at-most-once contract |
| `checkout_saga` | the multi-step state machine, compensation, and backoff |
| `abandoned_cart` | the deadline source and cancellation by delete |
| `warehouse_export` | day bucketing and the partitioned archive sink |

### 2.4 Conventional design

One component per layer, as the brief specifies, with the substitutions chosen so that each is a
swap rather than a simplification.

| Layer | Local | Production equivalent | Swap is |
|---|---|---|---|
| Serving | FastAPI + Uvicorn | same | identity |
| Transactional DB | Postgres 17 in Docker | same | identity |
| Durable execution | Temporal dev cluster | Temporal Cloud | a client address and credentials |
| Message bus | Redpanda | Kafka | identity (Kafka wire protocol) |
| ETL | Python consumer + SQL transforms | same, or dbt | identity |
| Warehouse | DuckDB | Snowflake / BigQuery | the SQL dialect and a connection |
| Object storage | local filesystem | S3 | one class behind a `put`/`get`/`list` protocol |

Choices that a reader should see stated rather than infer:

- **SQLAlchemy 2.0 async ORM plus Alembic**, not hand-written SQL. It is the mainstream choice for
  a FastAPI service and it is the more verbose one; picking the leaner option would have made the
  conventional side smaller and the comparison less representative. The delta is estimated in
  [section 6](#6-counting-methodology).
- **A transactional outbox**, not a direct publish from the request handler. Publishing to the bus
  and committing to the database as two operations is the dual-write bug; a good engineer does not
  ship it, so the outbox and its relay are counted.
- **SQL transform files with a small runner**, not dbt. dbt would move roughly the same logic into
  a project scaffold and add config; the estimate is in section 6.
- **No OpenTelemetry collector container.** The SDK is wired and exports over OTLP when an endpoint
  is configured; running the collector locally would add configuration without adding application
  code.

Everything runs from `make up` and the integration tests exercise the real flows: place an order,
read stats, run a checkout that fails at payment and assert the compensation, and fire an
abandonment timer against a compressed clock.

## 3. The Cambra implementation

[`tests/programs/storefront/v2.cambra`](../tests/programs/storefront/v2.cambra) — 207 lines of code
and 93 of comment. The diff from `v1.cambra` is the augmentation.

**Nothing in it runs.** It is rejected at lexing on line 123, inside `quote`, which V2 inherits from
V1 unchanged: a multi-line `if`/`else` in expression position whose `else:` sits at a shallower
indent than the branch above it, and the off-side rule has no continuation for a bracket-less
multi-line expression. A lex error aborts the run, so the surfaces V2 adds never reach a
diagnostic at all. Their blockers are pinned by four satellite programs instead, per the corpus
policy in [demo-programs.md](demo-programs.md#north-star-programs-and-corpus-policy).

| Satellite | Pins | Blocked at |
|---|---|---|
| [`external_call`](../tests/programs/external_call/) | the keyed outbound call and its at-most-once contract | lowering |
| [`abandoned_cart`](../tests/programs/abandoned_cart/) | the deadline source and cancellation by delete | lowering |
| [`checkout_saga`](../tests/programs/checkout_saga/) | the state machine, compensation, and backoff | parsing |
| [`warehouse_export`](../tests/programs/warehouse_export/) | day bucketing and the partitioned archive sink | lowering |

Each satellite's `mod.rs` carries its own dependency list. The gap list consolidated across all of
them is [section 7](#7-the-gap-list).

## 4. The conventional implementation

[`reference-app/`](../reference-app/) — 46 files: 1,385 lines of application code, 263 of tests,
and 37 of external-service stubs. It runs:

```bash
cd reference-app
make up      # eight services, then a readiness probe
make test    # 35 unit tests, then 17 end-to-end tests against the running stack
make down
```

`make up` takes about 30 seconds on a warm image cache and `make test` about two minutes. Both were
run from a clean `make down` before the numbers in this report were taken.

The end-to-end tests exercise the flows the brief names and a few more: an order priced by the flash
sale, the cost floor clamping a low-margin SKU, a 404 on an unknown SKU, a 422 on a negative
quantity from the framework rather than a handler, twenty concurrent orders against stock for twelve
of them, thirty concurrent orders racing for one promotion budget, a checkout that runs to
`confirmed`, a checkout whose payment is declined and whose reservation comes back, an abandonment
timer firing against a compressed clock, a checkout signal cancelling that timer, and an order line
travelling through the outbox, the topic, object storage, and the warehouse to the analytics
endpoint.

### Where the conventional side would not survive production as written

Named here rather than left for a reader to find.

- **The three external services are one stub process.** A payment processor, a warehouse API, and a
  transactional-email provider are all `storefront/payments/app.py`. It is counted separately (37
  lines, excluded) and its only application-visible behaviour is that `tok_fail` is declined.
- **No authentication or authorization anywhere.** Both implementations score zero, so the ratio is
  unaffected, but a real storefront has both and the conventional side would carry more of it:
  middleware, token validation, and a dependency on every route, against a refinement on the
  request type.
- **DuckDB is a single-writer embedded database.** The ETL writes it and the API opens it read-only.
  Snowflake or BigQuery removes that constraint; a second local writer would break it.
- **The Temporal dev cluster shares its Postgres with the application.** Temporal Cloud does not.
- **No OpenTelemetry collector.** The SDK is wired and exports when `OTLP_ENDPOINT` is set;
  running a collector locally would add configuration without adding application code.
- **The outbox relay polls.** At this scale that is correct; at higher throughput it becomes logical
  replication or a change-data-capture connector, which is more configuration, not less.
- **Retention, backups, and schema evolution on the warehouse are absent** on both sides.

### Choices a reader should see stated

- **SQLAlchemy 2.0 async ORM plus Alembic**, not hand-written SQL. It is the mainstream choice for a
  FastAPI service and it is the more verbose one. Raw `asyncpg` against a `schema.sql` would trade
  `models.py`'s 75 lines and the 124 generated ones for roughly 70 lines of DDL and a migration
  runner — about 130 lines off the conventional side, taking the headline from 6.7× to 6.1×.
- **A transactional outbox**, not a direct publish from the handler. Publishing to the bus and
  committing to the database as two operations is the dual-write bug. The outbox and its relay are
  59 lines.
- **SQL model files with a small runner**, not dbt. A dbt project for one model would add
  `dbt_project.yml`, `profiles.yml`, a `schema.yml`, and a `models/` tree — roughly 40 lines of
  configuration to replace 12 lines of runner, so this choice makes the conventional side smaller.
- **Row locks and read-committed isolation**, not serializable with a retry loop. An incrementally
  maintained `promo_spend` row is both the faster design and the direct counterpart of Cambra's
  `is_promo_spent` view. Serializable-plus-retry would have added about 25 lines of retry machinery
  to the `fault-tolerance` row; not using it makes the conventional side smaller.

Three of those four choices push the conventional total down. That is deliberate: where a judgment
call could go either way, it went the way that makes the comparison less flattering to Cambra.

## 5. Line counts by purpose

Produced by `reference-app/tools/count_loc.py`, which is committed and reproducible.

| Purpose | Cambra | Conventional | Ratio |
|---|---:|---:|---:|
| domain | 92 | 131 | 1.4× |
| serialization | 10 | 184 | 18.4× |
| connections | 4 | 92 | 23.0× |
| schema | 22 | 110 | 5.0× |
| fault-tolerance | 68 | 157 | 2.3× |
| flow-control | 0 | 54 | n/a |
| authorization | 0 | 0 | — |
| etl | 8 | 167 | 20.9× |
| observability | 0 | 46 | n/a |
| config-infra | 3 | 320 | 106.7× |
| tests-unit *(excluded)* | 0 | 84 | n/a |
| tests-integration *(excluded)* | 0 | 179 | n/a |
| generated | 0 | 124 | n/a |
| stubs *(excluded)* | 0 | 37 | n/a |
| **Application total** | **207** | **1385** | **6.7×** |
| **Everything, tests and stubs included** | **207** | **1685** | **8.1×** |

| | Cambra | Conventional |
|---|---:|---:|
| Files | 1 | 46 |
| Code lines classified by file glob | 0 | 1594 |
| Code lines classified by hand-written line range | 207 | 91 |
| Comment lines (not counted above) | 93 | 274 |

Derived figures used in [section 1](#1-summary):

| Figure | Cambra | Conventional | Ratio |
|---|---:|---:|---:|
| Application code | 207 | 1,385 | 6.7× |
| Domain logic alone | 92 | 131 | 1.4× |
| Everything except domain logic | 115 | 1,254 | 10.9× |
| Application plus end-to-end tests, assuming Cambra needs the same suite | 386 | 1,564 | 4.1× |
| Application, charging Cambra 45 lines for a deployment it does not have yet | 252 | 1,385 | 5.5× |
| Both adjustments together | 431 | 1,564 | 3.6× |

The `authorization` row is zero on both sides because neither implementation has any. It is kept in
the table rather than dropped, so that a reader can see it was considered and is missing.

## 6. Counting methodology

**The mechanical part.** `cloc` 2.10, `--by-file`, decides what is code, comment, and blank. The
script never overrides it. `.cambra` is mapped to Python's comment rules (`#` to end of line, no
block comments), which is exactly right for CHL. `.env.example` is mapped to INI. Comment lines are
reported but excluded from every count above: `v2.cambra` is a specification artifact and is
commented far more heavily than the Python, so counting comments would favour the conventional side
by an amount that has nothing to do with either language.

**The manual part.** `reference-app/tools/classification.json` assigns each file a purpose by glob,
and each mixed file a purpose per line range. The two mechanisms are reported separately in the
table above because they are not equally checkable: a glob assignment is verified by reading one
path, a range assignment by reading the range. **Of the Cambra side, all 207 lines are
range-classified**, because it is one file; on the conventional side, 91 of 1,685 lines are.

The script fails if any file in scope matches no rule, so nothing is silently omitted. Rerun it
with:

```bash
cd reference-app && make count      # or: python3 tools/count_loc.py --json
```

**Where the classification is arguable.** Three places, all in Cambra's favour or against it as
noted.

1. On the Cambra side a handler loop is API plumbing and domain logic in the same statements, and
   there is no line to split. Those loops are counted as `domain`, which inflates Cambra's `domain`
   row and deflates its `serialization` row. The conventional side's `api/` modules are counted as
   `serialization` because the domain logic there genuinely lives elsewhere. This makes the 1.4×
   domain ratio look worse for Cambra and the 18.4× serialization ratio look better; it does not
   move the total.
2. The saga's result handlers in `v2.cambra` advance state (domain) and compensate (fault
   tolerance) in the same transaction. They are counted as `fault-tolerance` by dominant purpose,
   matching `workflows.py` on the other side.
3. Cambra's four `http.call` bindings are counted as `connections`, matching the conventional side's
   `deps.py`, `db.py`, and `bus.py`. Counting them as `fault-tolerance` instead — the at-most-once
   contract is what they buy — would move 4 lines.

**What is excluded from the application total.** Tests on both sides, because Cambra has none and
cannot have any until the program compiles; and the external-service stubs, because a running
Cambra version would need the same stand-ins. Both are shown in the table so the exclusion is
visible rather than assumed.

**Generated code is its own row.** The 124 lines are Alembic's autogenerated initial migration (79),
its `env.py` scaffolding from `alembic init` with about six lines edited (30), and its
`script.py.mako` template (15). The catalog seed migration is hand-written — Alembic diffs schema,
not data — and is counted as `schema`.

## 7. The gap list

What the augmentation needs that CHL does not have. This is the deliverable that outlives the line
count.

Two of these are semantic holes and the rest are surface. That ratio is the finding: durable
execution turns out to need two primitives, and once state durability is a substrate property,
nothing else about it is irreducible.

### Semantic holes

| Gap | What is missing | Why it is not surface |
|---|---|---|
| **The outbound call** | A call to an external service whose result re-enters the graph, with at-most-once dispatch per key. `http.call` in `external_call`. | Sources are inputs and sinks are outputs; nothing in the model describes an effect whose result comes back. The durability contract — dispatch recorded before the call, result recorded before any consumer observes it — is what a workflow engine sells, and it has no expression here. |
| **The deadline source** | `clock.due(m)` over a `Mut(Map(K, Time), Txn)` variable. `abandoned_cart`. | A source whose arrivals are caused by the program's own state, unlike `stdin()` or `http_serve`. The cycle is well-founded by the key, which is the same causal-accessor argument the mutability substrate already makes, but nothing states it for sources. |

Both are shaped like something CHL already has, which is why they are two and not six. The outbound
call is `http.serve` reversed. The deadline is the watermark the history substrate already advances,
exposed as a source. What falls out of them without further surface: retry with backoff (a failed
result writes a new deadline and re-dispatches under a new attempt key — no loop, so it does not
wait on `while` lowering), compensation (an ordinary transaction the state machine reaches), and the
saga itself (a per-key state machine over transactional state, one `for` loop per event source).

### Library gaps

| Gap | Notes |
|---|---|
| Object-storage sink with a partition function (`store.parquet`) | The archive is the half of the ETL that crosses a boundary. Retention and cold storage are not met by an in-program view, so this is a gap, not a saving. |
| `Time` arithmetic (`clock.day`, `t + seconds`) | `Time` is a position in the commit order with no algebra. Day bucketing and a deadline offset both need one. |
| Map-entry deletion | Written `del m[k]` here, borrowed from Python. Nothing decides the spelling. Cancelling a timer is a delete, so the timer design needs it. |
| Metrics and structured logs | The conventional side spends 46 lines on observability; Cambra has no surface for any of it. The inspector observes a running program, which is not the same thing as an exported counter. |

### Already-tracked surface the augmentation also needs

Every one of these is in [demo-programs.md](demo-programs.md) or the
[spec](chl-spec.md#12-reserved-for-future-work) already: `import`, record terms `(f=v)`, map
literals `[k -> v]`, `Feed(…)` forward declarations, refinement syntax `{T where p(_)}`,
`static assert`, `requires Transaction` / `summon`, subscript assignment targets, `match` on a
variant, `FullMap`, the map comprehension `[k -> v for …]`, `k -> g` entry-pair iteration, and the
`http` module's response constructors.

### One open typing question the augmentation raises

`checkouts` is a `FullMap` whose key set grows as the program runs. Its totality is real — the
result source's domain is exactly the set of keys dispatched into `charges`, which is exactly the
set of keys `checkouts` holds — but `FullMap`'s earned domain is stated for a fixed key set
(`docs/chl-spec.md`, "6.3 Direction: collections as functions [Tentative]"), and that section's
`[Open]` marker already names the construction-site obligation this runs into.

## 8. What this comparison does and does not show

Written as the skeptical reader.

**You are comparing a program that does not compile against a system that runs.** This is the
objection that subsumes the others. The 207 lines were written against a language surface that is
mostly `[Decided]` or `[Sketched]`, and nobody has run a type checker over them, let alone a
workload. Code that has never been executed is systematically shorter than code that has, because
every bug fixed, every edge case discovered, and every operational surprise adds lines. The
conventional implementation has been through that process, in miniature, over the course of being
made to pass 17 end-to-end tests; the Cambra one has not. If the honest discount for that is 30%,
the ratio is 4.7×. If it is 100% — if you believe the exercise proves nothing until the compiler
catches up — that is a defensible position and this document does not argue against it.

**Two of the primitives the Cambra version depends on are designs written for this study.** The
outbound call and the deadline source were designed here, in [section 2.3](#23-cambra-design), and
have not been through the team's design process. They are argued from Cambra's existing model rather
than invented freely, which is the most that can be claimed for them. If either turns out to need
more machinery than the four and three lines it costs in `v2.cambra`, the Cambra side grows.

**The ETL saving is architectural, not linguistic.** The outbox, the topic, the consumer, the
loader, and the mart — 167 lines — exist because analytics lives in a different system from the
transactional store. Cambra's position is that it need not. That is a real architectural claim with
real consequences a reader may reject: analytical queries then contend with operational ones for the
same engine, retention policies for the two diverge, and the blast radius of a bad query is the
storefront. Every organisation that separated its warehouse from its database had reasons, and "the
language makes it unnecessary" answers none of them. Discount this row as far as you disagree.

**The `config-infra` row is not a language result.** 3 lines against 320 is the largest ratio in the
table and the least meaningful. Cambra has no deployment surface, so it has no Dockerfile, no
process supervision, no dependency manifest, and no environment configuration — not because they are
unnecessary but because they do not exist yet. Much of the conventional 320 is the cost of running
eight processes rather than one, which a single-process Cambra program genuinely avoids; a fair
estimate of what a deployed Cambra program would still need is 30 to 60 lines, which takes the
headline from 6.7× to between 5.8× and 5.2×. Do not quote 107×.

**The domain logic did not shrink much, and that is the most transferable result.** 92 against 131.
Whatever else is true, writing the business rules of a storefront takes about the same number of
lines in either. A reader who was promised a smaller application should note that the promise is
about the other 90% of it.

**One test suite does not shrink.** The 179 lines of end-to-end tests drive HTTP endpoints from
outside and would be almost identical against a Cambra implementation. The 84 lines of unit tests
would largely vanish, because the pricing contract they check is a `static assert` in the Cambra
version — but that substitution is only real once the compiler discharges it, which it does not.

**Both implementations are smaller than a production storefront.** No authentication, no
authorization, no rate limiting, no idempotency on the public API, no admin surface, no pagination,
no schema evolution, no backfill, no dead-letter handling, no runbooks. Three durable-execution use
cases that a real storefront needs — authorize-now/capture-at-ship, returns, and backorder
notification — were assessed and not built
([section 2.1](#21-which-storefront-use-cases-need-durable-execution)). Adding any of it adds to
both sides; whether it adds proportionally is unknown, and this study does
not answer it.

**A single application is a single data point.** It was chosen because it is the pitch's own
example, which makes it the right thing to measure and also the thing most likely to suit Cambra.
A CRUD-heavy application with little concurrency and no analytics would show a smaller ratio; a
pipeline-heavy one might show a larger. One measurement of one application, by one author who knew
which answer would be convenient, is worth exactly what that description suggests — which is why the
script, the classification, and both implementations are committed, so the next person can disagree
with the numbers rather than with the summary.

### What it does show

Three things survive every discount above.

1. **The saving is real and it is not in the domain logic.** Serialization at 18×, connection
   management at 23×, and data movement at 21× are large enough that no plausible correction to the
   method removes them. They are all the same phenomenon: code that exists because state crosses a
   boundary between systems that do not share a type system.
2. **Durable execution decomposes into two primitives.** Once state durability is a property of the
   substrate, what a workflow engine adds is an at-most-once external call and a deadline. Retry,
   backoff, compensation, and the saga state machine need no further surface. That finding stands
   whether or not the line count is quoted, and it is the part of this study most likely to be
   useful to the team.
3. **The gap list is priced.** Two semantic holes and four library gaps separate the north-star
   program from a running one. That list is short, and every item on it is named against a program
   and a test that goes red when it closes.
