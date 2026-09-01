"""End-to-end fixtures: an HTTP client against the running stack, and a reset.

These tests talk to the real services `make up` starts. Nothing is mocked; the
point of this suite is that the wiring between eight processes works.
"""

import asyncio
import os
from collections.abc import AsyncIterator

import httpx
import pytest
import pytest_asyncio
from sqlalchemy import text

from storefront.platform import db

API = os.environ.get("API_URL", "http://api:8080")

CATALOG_STOCK = {"tee-black": 500, "hoodie": 200, "poster": 1000}


@pytest_asyncio.fixture
async def client() -> AsyncIterator[httpx.AsyncClient]:
    async with httpx.AsyncClient(base_url=API, timeout=30.0) as c:
        yield c


@pytest_asyncio.fixture(autouse=True)
async def reset() -> AsyncIterator[None]:
    """Truncate the ledger and restore stock, so each test starts from the seed."""
    async with db.transaction() as s:
        await s.execute(text("TRUNCATE order_lines, outbox, checkouts, carts"))
        await s.execute(text("UPDATE promo_spend SET spent = 0"))
        for sku, qty in CATALOG_STOCK.items():
            await s.execute(
                text("UPDATE inventory SET qty = :qty WHERE sku = :sku"),
                {"qty": qty, "sku": sku},
            )
    yield


async def poll(fn, predicate, timeout: float = 60.0, interval: float = 0.5):
    """Wait for an eventually-consistent condition, or fail with what it last saw."""
    deadline = asyncio.get_running_loop().time() + timeout
    last = None
    while asyncio.get_running_loop().time() < deadline:
        last = await fn()
        if predicate(last):
            return last
        await asyncio.sleep(interval)
    pytest.fail(f"condition not reached within {timeout}s; last value: {last!r}")
