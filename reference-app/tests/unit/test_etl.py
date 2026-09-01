"""The ETL's landing, loading, and transform steps, without a broker."""

import duckdb

from storefront.etl import loader, transform
from storefront.etl.consumer import write_batch
from storefront.platform.objectstore import LocalObjectStore

ROWS = [
    {"id": 1, "sku": "tee-black", "qty": 2, "price": 25, "discount": 25},
    {"id": 2, "sku": "poster", "qty": 1, "price": 9, "discount": 1},
]


def test_batch_lands_as_a_day_partitioned_object(tmp_path):
    store = LocalObjectStore(tmp_path)
    key = write_batch(store, ROWS)
    assert key.startswith("order_lines/dt=")
    assert key.endswith(".parquet")


def test_load_then_transform_builds_the_mart(tmp_path):
    store = LocalObjectStore(tmp_path)
    write_batch(store, ROWS)
    conn = duckdb.connect(str(tmp_path / "w.duckdb"))
    assert loader.load_new_objects(conn, store) == 2
    transform.run(conn)
    rows = conn.execute("SELECT sku, revenue, units FROM daily_sku_revenue ORDER BY sku").fetchall()
    assert rows == [("poster", 9, 1), ("tee-black", 25, 2)]


def test_objects_are_loaded_once(tmp_path):
    store = LocalObjectStore(tmp_path)
    write_batch(store, ROWS)
    conn = duckdb.connect(str(tmp_path / "w.duckdb"))
    assert loader.load_new_objects(conn, store) == 2
    assert loader.load_new_objects(conn, store) == 0


def test_a_replayed_batch_does_not_double_count(tmp_path):
    """At-least-once delivery means the same order line can land twice."""
    store = LocalObjectStore(tmp_path)
    write_batch(store, ROWS)
    write_batch(store, ROWS)
    conn = duckdb.connect(str(tmp_path / "w.duckdb"))
    loader.load_new_objects(conn, store)
    transform.run(conn)
    total = conn.execute("SELECT SUM(revenue) FROM daily_sku_revenue").fetchone()[0]
    assert total == 34
