"""Kafka producer and consumer wrappers.

The wrappers exist so that connection lifetime is owned in one place: aiokafka
clients must be started and stopped, and a producer left running past process
exit loses whatever is still in its accumulator.
"""

import json
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager

from aiokafka import AIOKafkaConsumer, AIOKafkaProducer

from storefront.config import settings


@asynccontextmanager
async def producer() -> AsyncIterator[AIOKafkaProducer]:
    p = AIOKafkaProducer(
        bootstrap_servers=settings().kafka_bootstrap,
        enable_idempotence=True,
        acks="all",
        value_serializer=lambda v: json.dumps(v).encode(),
        key_serializer=lambda k: k.encode(),
    )
    await p.start()
    try:
        yield p
    finally:
        await p.stop()


@asynccontextmanager
async def consumer(topic: str, group: str) -> AsyncIterator[AIOKafkaConsumer]:
    c = AIOKafkaConsumer(
        topic,
        bootstrap_servers=settings().kafka_bootstrap,
        group_id=group,
        enable_auto_commit=False,
        auto_offset_reset="earliest",
        value_deserializer=lambda v: json.loads(v.decode()),
    )
    await c.start()
    try:
        yield c
    finally:
        await c.stop()
