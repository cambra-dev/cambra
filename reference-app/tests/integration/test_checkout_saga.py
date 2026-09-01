"""The checkout saga: the happy path, and the compensation when payment fails."""

from sqlalchemy import text

from storefront.platform import db
from tests.integration.conftest import poll


async def _stock(sku: str) -> int:
    async with db.session() as s:
        return await s.scalar(
            text("SELECT qty FROM inventory WHERE sku = :sku"), {"sku": sku}
        )


async def test_checkout_runs_to_confirmed(client):
    started = await client.post(
        "/checkout", json={"sku": "tee-black", "qty": 1, "payment_token": "tok_ok"}
    )
    assert started.status_code == 202
    checkout_id = started.json()["id"]

    final = await poll(
        lambda: client.get(f"/checkout/{checkout_id}"),
        lambda r: r.json()["stage"] in ("confirmed", "compensated"),
    )
    assert final.json()["stage"] == "confirmed"


async def test_checkout_reserves_stock(client):
    before = await _stock("tee-black")
    started = await client.post("/checkout", json={"sku": "tee-black", "qty": 3})
    await poll(
        lambda: client.get(f"/checkout/{started.json()['id']}"),
        lambda r: r.json()["stage"] == "confirmed",
    )
    assert await _stock("tee-black") == before - 3


async def test_payment_failure_compensates_the_reservation(client):
    before = await _stock("hoodie")
    started = await client.post(
        "/checkout", json={"sku": "hoodie", "qty": 4, "payment_token": "tok_fail"}
    )
    checkout_id = started.json()["id"]

    final = await poll(
        lambda: client.get(f"/checkout/{checkout_id}"),
        lambda r: r.json()["stage"] in ("confirmed", "compensated"),
    )
    assert final.json()["stage"] == "compensated"
    assert "declined" in (final.json()["detail"] or "")

    # The compensation is the point: the reservation went back.
    after = await poll(
        lambda: _stock("hoodie"), lambda qty: qty == before, timeout=30.0
    )
    assert after == before


async def test_checkout_of_an_unavailable_sku_compensates_nothing(client):
    await client.post("/order", json={"sku": "hoodie", "qty": 200})
    before = await _stock("hoodie")
    started = await client.post("/checkout", json={"sku": "hoodie", "qty": 1})
    final = await poll(
        lambda: client.get(f"/checkout/{started.json()['id']}"),
        lambda r: r.json()["stage"] in ("confirmed", "compensated"),
    )
    assert final.json()["stage"] == "compensated"
    assert await _stock("hoodie") == before
