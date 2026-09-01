"""The ETL process: consume, land, load, transform, repeat.

Consuming and loading run concurrently because they have different natural
periods — the consumer is driven by arrivals, the loader by how often the
warehouse should be refreshed.
"""

import asyncio
from pathlib import Path

import duckdb

from storefront.config import settings
from storefront.etl import consumer, loader, transform
from storefront.platform.objectstore import LocalObjectStore
from storefront.platform.observability import configure, logger

log = logger(__name__)
LOAD_INTERVAL_SECONDS = 5.0


async def _load_loop(store: LocalObjectStore, stop: asyncio.Event) -> None:
    Path(settings().warehouse_path).parent.mkdir(parents=True, exist_ok=True)
    while not stop.is_set():
        await asyncio.sleep(LOAD_INTERVAL_SECONDS)
        conn = duckdb.connect(settings().warehouse_path)
        try:
            if await asyncio.to_thread(loader.load_new_objects, conn, store):
                await asyncio.to_thread(transform.run, conn)
        finally:
            conn.close()


async def main() -> None:
    configure("storefront-etl")
    store = LocalObjectStore(settings().object_store_root)
    stop = asyncio.Event()
    log.info("etl.start", root=settings().object_store_root)
    await asyncio.gather(consumer.run(store, stop), _load_loop(store, stop))


if __name__ == "__main__":
    asyncio.run(main())
