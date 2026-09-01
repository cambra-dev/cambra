"""Object storage to the warehouse.

Objects are loaded once: `_loaded_objects` records every key already ingested,
which is what makes the pipeline's at-least-once delivery safe. The order-line
id is the deduplication key within a batch, for the same reason.
"""

import io

import duckdb
import pyarrow.parquet as pq

from storefront.platform.objectstore import ObjectStore
from storefront.platform.observability import ETL_ROWS, logger

log = logger(__name__)

BOOTSTRAP = """
CREATE TABLE IF NOT EXISTS _loaded_objects (key VARCHAR PRIMARY KEY);
CREATE TABLE IF NOT EXISTS raw_order_lines (
    id BIGINT,
    sku VARCHAR,
    qty BIGINT,
    price BIGINT,
    discount BIGINT,
    ingested_at TIMESTAMPTZ
);
"""


def load_new_objects(conn: duckdb.DuckDBPyConnection, store: ObjectStore) -> int:
    conn.execute(BOOTSTRAP)
    loaded = {row[0] for row in conn.execute("SELECT key FROM _loaded_objects").fetchall()}
    total = 0
    for key in store.list_keys("order_lines"):
        if key in loaded:
            continue
        # DuckDB resolves a bare table name in SQL against the caller's Python
        # frame, so `arrow_table` below is this local read zero-copy.
        arrow_table = pq.read_table(io.BytesIO(store.get(key)))
        conn.execute(
            """
            INSERT INTO raw_order_lines
            SELECT * FROM arrow_table
            WHERE id NOT IN (SELECT id FROM raw_order_lines)
            """
        )
        conn.execute("INSERT INTO _loaded_objects VALUES (?)", [key])
        total += arrow_table.num_rows
    if total:
        ETL_ROWS.labels(stage="loaded").inc(total)
        log.info("etl.loaded", rows=total)
    return total
