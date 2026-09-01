"""Placing an order: reserve, price, record, and enqueue for the warehouse.

The whole body is one transaction. It takes two row locks — the inventory row in
`reserve`, then the promotion counter — always in that order, so two concurrent
orders queue rather than deadlock.

The promotion counter is what makes the budget safe: reading it under a lock and
incrementing it in the same transaction means two orders cannot both spend the
last of it.
"""

from sqlalchemy import func, select
from sqlalchemy.ext.asyncio import AsyncSession

from storefront.config import settings
from storefront.domain import inventory, pricing
from storefront.models import OrderLine, Outbox, PromoSpend

PROMO_ROW = 1


async def place(session: AsyncSession, sku: str, qty: int) -> pricing.Quote:
    item = await inventory.load_item(session, sku)
    await inventory.reserve(session, sku, qty)

    spend = await session.scalar(
        select(PromoSpend).where(PromoSpend.id == PROMO_ROW).with_for_update()
    )
    quote = pricing.quote(
        item, qty, pricing.promo_spent(spend.spent, settings().promo_budget)
    )
    spend.spent += quote.discount

    line = OrderLine(sku=sku, qty=qty, price=quote.price, discount=quote.discount)
    session.add(line)
    await session.flush()
    session.add(
        Outbox(
            topic=settings().order_lines_topic,
            key=sku,
            payload={
                "id": line.id,
                "sku": sku,
                "qty": qty,
                "price": quote.price,
                "discount": quote.discount,
            },
        )
    )
    return quote


async def revenue_by_sku(session: AsyncSession) -> dict[str, int]:
    rows = await session.execute(
        select(OrderLine.sku, func.sum(OrderLine.price)).group_by(OrderLine.sku)
    )
    return {sku: int(total) for sku, total in rows}
