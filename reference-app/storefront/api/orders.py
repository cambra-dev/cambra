"""Order intake, restock, and the revenue rollup.

These are the north-star's three endpoints and they are single transactions, not
workflows: routing an ACID read-modify-write through a durable-execution engine
buys nothing and costs a round trip.
"""

from fastapi import APIRouter

from storefront.api.deps import Session
from storefront.domain import inventory, orders
from storefront.platform import db
from storefront.platform.observability import ORDERS
from storefront.schemas import (
    OrderRequest,
    OrderResponse,
    RestockRequest,
    RestockResponse,
    StatsResponse,
)

router = APIRouter()


@router.post("/order", response_model=OrderResponse)
async def place_order(body: OrderRequest) -> OrderResponse:
    try:
        async with db.transaction() as s:
            quote = await orders.place(s, body.sku, body.qty)
    except Exception:
        ORDERS.labels(outcome="rejected").inc()
        raise
    ORDERS.labels(outcome="placed").inc()
    return OrderResponse(price=quote.price, discount=quote.discount)


@router.post("/restock", response_model=RestockResponse)
async def restock(body: RestockRequest) -> RestockResponse:
    async with db.transaction() as s:
        qty = await inventory.release(s, body.sku, body.qty)
    return RestockResponse(sku=body.sku, qty=qty)


@router.get("/stats", response_model=StatsResponse)
async def stats(s: Session) -> StatsResponse:
    # A repeatable-read read-only snapshot: the rollup must not see half of a
    # concurrent order. This is the conventional spelling of the Cambra
    # program's "as of this request's own transaction time".
    await s.connection(
        execution_options={"isolation_level": "REPEATABLE READ", "postgresql_readonly": True}
    )
    return StatsResponse(revenue=await orders.revenue_by_sku(s))
