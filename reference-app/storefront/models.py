"""The transactional schema.

Two invariants live in the database rather than in application code, because
the application is not the only writer: `inventory.qty >= 0` (the Cambra
program's `Qty` refinement) and `catalog.price >= catalog.cost` (its
`ItemPricing` record refinement). A check constraint is the nearest a
conventional stack gets to either.
"""

from datetime import datetime

from sqlalchemy import (
    BigInteger,
    CheckConstraint,
    DateTime,
    ForeignKey,
    Index,
    Integer,
    String,
    func,
)
from sqlalchemy.dialects.postgresql import JSONB
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column


class Base(DeclarativeBase):
    pass


class CatalogItem(Base):
    __tablename__ = "catalog"
    __table_args__ = (CheckConstraint("price >= cost", name="ck_catalog_above_cost"),)

    sku: Mapped[str] = mapped_column(String(64), primary_key=True)
    price: Mapped[int] = mapped_column(Integer)
    cost: Mapped[int] = mapped_column(Integer)


class Inventory(Base):
    __tablename__ = "inventory"
    __table_args__ = (CheckConstraint("qty >= 0", name="ck_inventory_nonneg"),)

    sku: Mapped[str] = mapped_column(ForeignKey("catalog.sku"), primary_key=True)
    qty: Mapped[int] = mapped_column(Integer)


class OrderLine(Base):
    __tablename__ = "order_lines"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    sku: Mapped[str] = mapped_column(ForeignKey("catalog.sku"))
    qty: Mapped[int] = mapped_column(Integer)
    price: Mapped[int] = mapped_column(Integer)
    discount: Mapped[int] = mapped_column(Integer)
    created_at: Mapped[datetime] = mapped_column(
        DateTime(timezone=True), server_default=func.now()
    )


# `/stats` groups by SKU on every read.
Index("ix_order_lines_sku", OrderLine.sku)


class PromoSpend(Base):
    """The flash sale's cumulative forgone revenue, maintained incrementally.

    A single row, locked by every order that prices under the sale. Summing
    `order_lines.discount` on each order would give the same answer and read the
    whole ledger to do it; this is the conventional spelling of the Cambra
    program's `is_promo_spent` view, which the runtime is free to materialize.

    Locking one row serializes every discounted order behind it. That is a real
    cost of a budget that must not be overspent, and it is the same
    serialization the Cambra version's transactional read imposes.
    """

    __tablename__ = "promo_spend"

    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    spent: Mapped[int] = mapped_column(Integer, default=0)


class Cart(Base):
    __tablename__ = "carts"

    id: Mapped[str] = mapped_column(String(64), primary_key=True)
    sku: Mapped[str] = mapped_column(ForeignKey("catalog.sku"))
    qty: Mapped[int] = mapped_column(Integer)
    status: Mapped[str] = mapped_column(String(16), default="open")
    created_at: Mapped[datetime] = mapped_column(
        DateTime(timezone=True), server_default=func.now()
    )


class Checkout(Base):
    __tablename__ = "checkouts"

    id: Mapped[str] = mapped_column(String(64), primary_key=True)
    sku: Mapped[str] = mapped_column(ForeignKey("catalog.sku"))
    qty: Mapped[int] = mapped_column(Integer)
    amount: Mapped[int] = mapped_column(Integer)
    stage: Mapped[str] = mapped_column(String(24))
    attempt: Mapped[int] = mapped_column(Integer, default=0)
    detail: Mapped[str | None] = mapped_column(String(256), nullable=True)
    updated_at: Mapped[datetime] = mapped_column(
        DateTime(timezone=True), server_default=func.now(), onupdate=func.now()
    )


class Outbox(Base):
    """Rows written in the same transaction as the fact they describe.

    Publishing to the bus and committing to the database as two operations is
    the dual-write bug: either can succeed alone. The relay reads committed rows
    only, so a message exists on the topic if and only if its order line exists
    in the ledger.
    """

    __tablename__ = "outbox"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    topic: Mapped[str] = mapped_column(String(128))
    key: Mapped[str] = mapped_column(String(128))
    payload: Mapped[dict] = mapped_column(JSONB)
    created_at: Mapped[datetime] = mapped_column(
        DateTime(timezone=True), server_default=func.now()
    )
    published_at: Mapped[datetime | None] = mapped_column(
        DateTime(timezone=True), nullable=True
    )


Index("ix_outbox_unpublished", Outbox.id, postgresql_where=Outbox.published_at.is_(None))
