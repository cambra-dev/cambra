"""Stock reservation and restock, as SQL against a locked row.

Both take the row lock before reading, so the read-modify-write cannot
interleave with a concurrent one. The `qty >= 0` check constraint is the backstop
if a future caller forgets: it makes overselling an error the database refuses,
which is the closest a conventional stack comes to the Cambra program's `Qty`
refinement making it ill-typed.
"""

from sqlalchemy import select, update
from sqlalchemy.ext.asyncio import AsyncSession

from storefront.domain.errors import OutOfStock, UnknownSku
from storefront.domain.pricing import Item
from storefront.models import CatalogItem, Inventory


async def load_item(session: AsyncSession, sku: str) -> Item:
    row = await session.get(CatalogItem, sku)
    if row is None:
        raise UnknownSku(sku)
    return Item(sku=row.sku, price=row.price, cost=row.cost)


async def reserve(session: AsyncSession, sku: str, qty: int) -> None:
    stock = await session.scalar(
        select(Inventory.qty).where(Inventory.sku == sku).with_for_update()
    )
    if stock is None:
        raise UnknownSku(sku)
    if stock < qty:
        raise OutOfStock(sku)
    await session.execute(
        update(Inventory).where(Inventory.sku == sku).values(qty=stock - qty)
    )


async def release(session: AsyncSession, sku: str, qty: int) -> int:
    """Add `qty` back and return the new stock level."""
    stock = await session.scalar(
        select(Inventory.qty).where(Inventory.sku == sku).with_for_update()
    )
    if stock is None:
        raise UnknownSku(sku)
    await session.execute(
        update(Inventory).where(Inventory.sku == sku).values(qty=stock + qty)
    )
    return stock + qty
