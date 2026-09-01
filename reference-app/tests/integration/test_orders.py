"""Order intake, the invariants, and the stats rollup."""

import asyncio

from tests.integration.conftest import poll


async def test_order_is_priced_by_the_flash_sale(client):
    response = await client.post("/order", json={"sku": "tee-black", "qty": 2})
    assert response.status_code == 200
    assert response.json() == {"price": 25, "discount": 25}


async def test_low_margin_item_clamps_at_cost(client):
    response = await client.post("/order", json={"sku": "poster", "qty": 1})
    assert response.json()["price"] == 9


async def test_unknown_sku_is_404(client):
    response = await client.post("/order", json={"sku": "nope", "qty": 1})
    assert response.status_code == 404


async def test_negative_quantity_is_refused_at_the_boundary(client):
    response = await client.post("/order", json={"sku": "tee-black", "qty": -1})
    assert response.status_code == 422


async def test_oversell_is_409_and_stock_never_goes_negative(client):
    await client.post("/restock", json={"sku": "hoodie", "qty": 0})
    drain = await client.post("/order", json={"sku": "hoodie", "qty": 200})
    assert drain.status_code == 200
    response = await client.post("/order", json={"sku": "hoodie", "qty": 1})
    assert response.status_code == 409


async def test_concurrent_orders_never_oversell(client):
    """Twenty concurrent orders against stock for twelve of them."""
    await client.post("/order", json={"sku": "hoodie", "qty": 188})
    results = await asyncio.gather(
        *(client.post("/order", json={"sku": "hoodie", "qty": 1}) for _ in range(20))
    )
    codes = [r.status_code for r in results]
    assert codes.count(200) == 12
    assert codes.count(409) == 8


async def test_promo_budget_is_spent_once(client):
    """Cumulative discount stops at the budget however many orders race for it.

    Each order of 4 tees lists at 100 and sells at 50, spending 50 of the 1000
    budget. Twenty orders exhaust it; the last ten pay list. If two orders could
    both see the budget as unspent, revenue would come out below 2000.
    """
    results = await asyncio.gather(
        *(client.post("/order", json={"sku": "tee-black", "qty": 4}) for _ in range(30))
    )
    assert all(r.status_code == 200 for r in results)
    stats = (await client.get("/stats")).json()["revenue"]
    assert stats["tee-black"] == 20 * 50 + 10 * 100


async def test_stats_reflects_committed_orders(client):
    await client.post("/order", json={"sku": "tee-black", "qty": 2})
    await client.post("/order", json={"sku": "poster", "qty": 1})
    stats = (await client.get("/stats")).json()["revenue"]
    assert stats == {"tee-black": 25, "poster": 9}


async def test_restock_adds_stock(client):
    before = await client.post("/order", json={"sku": "hoodie", "qty": 200})
    assert before.status_code == 200
    assert (await client.post("/order", json={"sku": "hoodie", "qty": 1})).status_code == 409
    await client.post("/restock", json={"sku": "hoodie", "qty": 5})
    assert (await client.post("/order", json={"sku": "hoodie", "qty": 1})).status_code == 200


async def test_orders_reach_the_warehouse(client):
    await client.post("/order", json={"sku": "tee-black", "qty": 2})
    rows = await poll(
        lambda: client.get("/analytics/daily-revenue"),
        lambda r: any(row["sku"] == "tee-black" for row in r.json()["rows"]),
    )
    tee = next(row for row in rows.json()["rows"] if row["sku"] == "tee-black")
    assert tee["units"] >= 2
