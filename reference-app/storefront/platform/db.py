"""Engine, session factory, and transaction scopes.

Every read-modify-write in the application takes a row lock before reading, so
read-committed is the right isolation level throughout: the lock blocks rather
than aborting, and there is no serialization failure to retry. Lock order is
inventory row, then the promotion counter, in every path that takes both.
"""

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager

from sqlalchemy.ext.asyncio import AsyncSession, async_sessionmaker, create_async_engine

from storefront.config import settings

_engine = create_async_engine(
    settings().database_url,
    pool_size=10,
    max_overflow=10,
    pool_pre_ping=True,
    pool_recycle=300,
)
_session_factory = async_sessionmaker(_engine, expire_on_commit=False)


@asynccontextmanager
async def session() -> AsyncIterator[AsyncSession]:
    async with _session_factory() as s:
        yield s


@asynccontextmanager
async def transaction() -> AsyncIterator[AsyncSession]:
    async with _session_factory() as s, s.begin():
        yield s


async def dispose() -> None:
    await _engine.dispose()
