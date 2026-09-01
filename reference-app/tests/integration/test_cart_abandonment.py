"""The abandonment timer, against a clock compressed to seconds.

`ABANDON_AFTER_SECONDS` is configuration, so the test drives the real timer
rather than a fake one: the same `wait_condition` runs, with a deadline it can
outlive. The 24-hour production value differs only in the number.
"""

import asyncio

from sqlalchemy import text

from storefront.config import settings
from storefront.platform import db
from tests.integration.conftest import poll


async def _cart_status(cart_id: str) -> str | None:
    async with db.session() as s:
        return await s.scalar(
            text("SELECT status FROM carts WHERE id = :id"), {"id": cart_id}
        )


async def test_an_untouched_cart_is_abandoned_when_the_timer_fires(client):
    cart = await client.post("/carts", json={"sku": "tee-black", "qty": 1})
    assert cart.status_code == 201
    cart_id = cart.json()["id"]

    status = await poll(
        lambda: _cart_status(cart_id), lambda s: s == "abandoned", timeout=90.0
    )
    assert status == "abandoned"


async def test_checking_out_cancels_the_timer(client):
    cart = await client.post("/carts", json={"sku": "tee-black", "qty": 1})
    cart_id = cart.json()["id"]

    checkout = await client.post(
        "/checkout", json={"sku": "tee-black", "qty": 1, "cart_id": cart_id}
    )
    assert checkout.status_code == 202
    assert await _cart_status(cart_id) == "checked_out"

    await poll(
        lambda: client.get(f"/checkout/{checkout.json()['id']}"),
        lambda r: r.json()["stage"] == "confirmed",
    )
    # Outlive the deadline the cancelled timer would have fired at. The signal
    # beat it, so the cart stays checked out.
    await asyncio.sleep(settings().abandon_after_seconds + 5)
    assert await _cart_status(cart_id) == "checked_out"


async def test_checkout_against_an_unknown_cart_is_404(client):
    response = await client.post(
        "/checkout", json={"sku": "tee-black", "qty": 1, "cart_id": "nope"}
    )
    assert response.status_code == 404
