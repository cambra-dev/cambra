"""Publishes committed outbox rows to the bus.

At-least-once by construction: the row is marked published after the broker
acknowledges, so a crash in between republishes. Consumers deduplicate on the
order-line id, which is the trade every outbox makes.
"""

import asyncio
from datetime import UTC, datetime

from sqlalchemy import func, select, update

from storefront.config import settings
from storefront.models import Outbox
from storefront.platform import bus, db
from storefront.platform.observability import OUTBOX_LAG, configure, logger

log = logger(__name__)
BATCH = 200


async def _drain(producer) -> int:
    async with db.transaction() as s:
        rows = (
            await s.scalars(
                select(Outbox)
                .where(Outbox.published_at.is_(None))
                .order_by(Outbox.id)
                .limit(BATCH)
                .with_for_update(skip_locked=True)
            )
        ).all()
        now = datetime.now(UTC)
        for row in rows:
            await producer.send_and_wait(row.topic, row.payload, key=row.key)
            OUTBOX_LAG.observe((now - row.created_at).total_seconds())
        if rows:
            await s.execute(
                update(Outbox)
                .where(Outbox.id.in_([r.id for r in rows]))
                .values(published_at=func.now())
            )
    return len(rows)


async def main() -> None:
    configure("storefront-relay")
    log.info("relay.start", topic=settings().order_lines_topic)
    async with bus.producer() as producer:
        while True:
            published = await _drain(producer)
            if published == 0:
                await asyncio.sleep(settings().relay_poll_seconds)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    finally:
        asyncio.run(db.dispose())
