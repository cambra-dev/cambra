"""Shared request dependencies: a database session and a Temporal client.

The Temporal client is per-process, not per-request: it multiplexes over one
gRPC connection and creating one per request would spend a handshake on every
checkout.
"""

from collections.abc import AsyncIterator
from typing import Annotated

from fastapi import Depends
from sqlalchemy.ext.asyncio import AsyncSession
from temporalio.client import Client

from storefront.config import settings
from storefront.platform import db

_client: Client | None = None


async def temporal_client() -> Client:
    global _client
    if _client is None:
        _client = await Client.connect(
            settings().temporal_target, namespace=settings().temporal_namespace
        )
    return _client


async def session() -> AsyncIterator[AsyncSession]:
    async with db.session() as s:
        yield s


Session = Annotated[AsyncSession, Depends(session)]
Temporal = Annotated[Client, Depends(temporal_client)]
