"""The object-store protocol, against the local implementation."""

from storefront.platform.objectstore import LocalObjectStore


def test_put_get_roundtrip(tmp_path):
    store = LocalObjectStore(tmp_path)
    store.put("order_lines/dt=2026-01-01/a.parquet", b"payload")
    assert store.get("order_lines/dt=2026-01-01/a.parquet") == b"payload"


def test_list_is_prefix_scoped_and_sorted(tmp_path):
    store = LocalObjectStore(tmp_path)
    store.put("order_lines/dt=2026-01-02/b", b"b")
    store.put("order_lines/dt=2026-01-01/a", b"a")
    store.put("other/c", b"c")
    assert store.list_keys("order_lines") == [
        "order_lines/dt=2026-01-01/a",
        "order_lines/dt=2026-01-02/b",
    ]


def test_missing_prefix_lists_empty(tmp_path):
    assert LocalObjectStore(tmp_path).list_keys("order_lines") == []


def test_partial_writes_are_invisible(tmp_path):
    store = LocalObjectStore(tmp_path)
    store.put("order_lines/x", b"x")
    (tmp_path / "order_lines" / "y.tmp").write_bytes(b"half")
    assert store.list_keys("order_lines") == ["order_lines/x"]
