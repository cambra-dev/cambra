"""Topic to object storage: batch order lines into day-partitioned Parquet.

Batching is by row count or elapsed time, whichever comes first, because a
warehouse loaded from one object per row is a warehouse of small files. Offsets
are committed after the object lands, so a crash replays the batch and the
loader deduplicates on order-line id.
"""

import asyncio
import io
import uuid
from datetime import UTC, datetime

import pyarrow as pa
import pyarrow.parquet as pq

from storefront.config import settings
from storefront.platform import bus
from storefront.platform.objectstore import ObjectStore
from storefront.platform.observability import ETL_ROWS, logger

log = logger(__name__)

SCHEMA = pa.schema(
    [
        ("id", pa.int64()),
        ("sku", pa.string()),
        ("qty", pa.int64()),
        ("price", pa.int64()),
        ("discount", pa.int64()),
        ("ingested_at", pa.timestamp("us", tz="UTC")),
    ]
)


def _object_key(day: str) -> str:
    return f"order_lines/dt={day}/{uuid.uuid4().hex}.parquet"


def write_batch(store: ObjectStore, rows: list[dict]) -> str:
    now = datetime.now(UTC)
    table = pa.Table.from_pylist(
        [{**row, "ingested_at": now} for row in rows], schema=SCHEMA
    )
    buffer = io.BytesIO()
    pq.write_table(table, buffer, compression="snappy")
    key = _object_key(now.date().isoformat())
    store.put(key, buffer.getvalue())
    ETL_ROWS.labels(stage="landed").inc(len(rows))
    log.info("etl.batch", key=key, rows=len(rows))
    return key


async def run(store: ObjectStore, stop: asyncio.Event) -> None:
    async with bus.consumer(settings().order_lines_topic, "storefront-etl") as consumer:
        batch: list[dict] = []
        deadline = asyncio.get_running_loop().time() + settings().etl_batch_max_seconds
        while not stop.is_set():
            timeout = max(0.05, deadline - asyncio.get_running_loop().time())
            polled = await consumer.getmany(timeout_ms=int(timeout * 1000))
            for records in polled.values():
                batch.extend(r.value for r in records)

            full = len(batch) >= settings().etl_batch_max_rows
            expired = asyncio.get_running_loop().time() >= deadline
            if batch and (full or expired):
                write_batch(store, batch)
                await consumer.commit()
                batch = []
            if expired:
                deadline = (
                    asyncio.get_running_loop().time() + settings().etl_batch_max_seconds
                )
