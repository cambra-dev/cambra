# Reference-app comparison: Cambra vs. an off-the-shelf stack

Status: **design recorded, implementations in progress.** Sections 5–8 carry the measurement and
are filled in once both implementations are complete.

This study builds one application twice — once in Cambra, once on a conventional stack — and counts
lines by purpose. The application is the storefront north-star
([`tests/programs/storefront/`](../tests/programs/storefront/)) augmented with durable execution and
an ETL-to-warehouse path.

The number is for a slide, so it has to survive a hostile reading. Everything that would flatter
Cambra without being true is called out where it occurs, and
[What this comparison does and does not show](#8-what-this-comparison-does-and-does-not-show)
is written from the skeptic's side.

## 1. Summary

_Filled in once both implementations are counted._

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
8. `POST /carts`, `POST /carts/{id}/lines` — a cart with an abandonment deadline. Checking out
   cancels it; firing it emits an abandonment event and releases the cart's soft holds.

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
  attempt key. It needs no loop, so it does not wait on `while` lowering. This is a result worth
  stating plainly: the retry construct that a workflow SDK provides as a configuration object is,
  in an event-driven dataflow language, two writes.
- **Compensation** is an ordinary transaction that the saga's state machine reaches. What durable
  execution adds is not the compensating step but the guarantee it runs, and that guarantee is the
  durability of the saga state — a `Mut(Map(K, V), Txn)` — plus the at-most-once call contract
  above.
- **The saga itself** is a per-key state machine over transactional state, advanced by one `for`
  loop per event source. No orchestration construct appears.

The finding behind all three: once state durability is a substrate property and external calls have
an at-most-once contract, durable execution has no remaining irreducible content. Cambra's state
durability is **[Sketched]**, not implemented ([design.md](design.md)), so this is a claim about
the model, not about a running system.

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

_In progress._

## 4. The conventional implementation

_In progress._

## 5. Line counts by purpose

_In progress._

## 6. Counting methodology

_In progress._

## 7. The gap list

_In progress._

## 8. What this comparison does and does not show

_In progress._
