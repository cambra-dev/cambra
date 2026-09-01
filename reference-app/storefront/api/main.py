"""The HTTP application: routers, error mapping, and the metrics endpoint."""

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager

from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse, Response
from opentelemetry.instrumentation.fastapi import FastAPIInstrumentor
from prometheus_client import CONTENT_TYPE_LATEST, generate_latest

from storefront.api import analytics, carts, checkout, orders
from storefront.domain.errors import DomainError
from storefront.platform import db
from storefront.platform.observability import configure


@asynccontextmanager
async def lifespan(_: FastAPI) -> AsyncIterator[None]:
    configure("storefront-api")
    yield
    await db.dispose()


app = FastAPI(title="Storefront", lifespan=lifespan)
app.include_router(orders.router)
app.include_router(carts.router)
app.include_router(checkout.router)
app.include_router(analytics.router)
FastAPIInstrumentor.instrument_app(app)


@app.exception_handler(DomainError)
async def domain_error(_: Request, exc: DomainError) -> JSONResponse:
    return JSONResponse(status_code=exc.status_code, content={"detail": str(exc)})


@app.get("/health")
async def health() -> dict[str, str]:
    return {"status": "ok"}


@app.get("/metrics")
async def metrics() -> Response:
    return Response(generate_latest(), media_type=CONTENT_TYPE_LATEST)
