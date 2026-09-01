# Storefront — the conventional implementation

The storefront application on an off-the-shelf stack, built as the comparison
arm for [`docs/REPORT.md`](../docs/REPORT.md).

Not part of the Rust build. `ci.sh` does not build, lint, or test anything here;
the one gate whose scope is the whole tree is `shellcheck`, and this directory
contains no shell scripts — the entry points are a `Makefile` and Python
modules. Adding a `.sh` here would put it under `shellcheck -a -o all`.

## Run it

```bash
make up             # build and start everything, then wait for readiness
make test           # unit tests, then end-to-end tests against the running stack
make down           # stop and delete volumes
```

`make up` runs migrations once, then starts eight long-running services:
Postgres, Redpanda, a Temporal dev cluster, the API, the Temporal worker, the
outbox relay, the ETL process, and a stub standing in for the three external
services the checkout saga calls. It returns when all of them answer.

## The endpoints

| Method | Path | What it does |
|---|---|---|
| `POST` | `/order` | Reserve stock, price the line, record it |
| `POST` | `/restock` | Add stock |
| `GET` | `/stats` | Revenue per SKU from a snapshot-consistent read |
| `POST` | `/carts` | Open a cart and start its abandonment timer |
| `POST` | `/checkout` | Start the checkout saga |
| `GET` | `/checkout/{id}` | Where the saga got to |
| `GET` | `/analytics/daily-revenue` | The warehouse mart |
| `GET` | `/metrics` | Prometheus exposition |

`payment_token` on `POST /checkout` takes `tok_ok` or `tok_fail`; `tok_fail` is
declined by the stub processor, which is how the compensation path is reached.

## Layout

| Path | Layer |
|---|---|
| `storefront/api/` | FastAPI routers |
| `storefront/domain/` | Pricing, inventory, order placement |
| `storefront/platform/` | Database, bus, object store, observability |
| `storefront/temporal_app/` | Workflows, activities, worker |
| `storefront/etl/` | Consumer, loader, SQL models |
| `storefront/payments/` | Stub external services (not application code) |
| `migrations/` | Alembic |
| `tests/` | Unit and end-to-end |
| `tools/` | The line counter and the readiness probe |

## Production substitutions

Every local component is a swap for a managed one, not a simplification:
Temporal dev cluster for Temporal Cloud, Redpanda for Kafka (same wire
protocol), DuckDB for Snowflake or BigQuery, and the local filesystem for S3
behind the `put`/`get`/`list_keys` protocol in
`storefront/platform/objectstore.py`. `docs/REPORT.md` says where a substitution
would not survive production.
