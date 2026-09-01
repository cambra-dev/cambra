"""The worker process: one task queue, both workflows, every activity."""

import asyncio

from temporalio.client import Client
from temporalio.worker import Worker

from storefront.config import settings
from storefront.platform import db
from storefront.platform.observability import configure, logger
from storefront.temporal_app import activities
from storefront.temporal_app.workflows import CartAbandonmentWorkflow, CheckoutWorkflow

ACTIVITIES = [
    activities.reserve_inventory,
    activities.release_inventory,
    activities.authorize_payment,
    activities.void_authorization,
    activities.create_fulfilment,
    activities.send_confirmation,
    activities.record_stage,
    activities.record_abandonment,
]


async def main() -> None:
    configure("storefront-worker")
    client = await Client.connect(
        settings().temporal_target, namespace=settings().temporal_namespace
    )
    logger(__name__).info("worker.start", task_queue=settings().task_queue)
    async with Worker(
        client,
        task_queue=settings().task_queue,
        workflows=[CheckoutWorkflow, CartAbandonmentWorkflow],
        activities=ACTIVITIES,
    ):
        await asyncio.Future()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    finally:
        asyncio.run(db.dispose())
