"""Structured logging, Prometheus metrics, and OTLP tracing.

One module because the three are configured together at process start and
nothing else in the application should know which library provides which.
"""

import logging

import structlog
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from prometheus_client import Counter, Histogram

from storefront.config import settings

ORDERS = Counter("storefront_orders_total", "Order attempts", ["outcome"])
CHECKOUTS = Counter("storefront_checkouts_total", "Checkout saga terminations", ["stage"])
EXTERNAL_CALLS = Counter(
    "storefront_external_calls_total", "Outbound service calls", ["service", "outcome"]
)
OUTBOX_LAG = Histogram("storefront_outbox_lag_seconds", "Outbox publish latency")
ETL_ROWS = Counter("storefront_etl_rows_total", "Rows moved by the ETL", ["stage"])


def configure(service_name: str) -> None:
    logging.basicConfig(level=settings().log_level, format="%(message)s")
    structlog.configure(
        processors=[
            structlog.contextvars.merge_contextvars,
            structlog.processors.add_log_level,
            structlog.processors.TimeStamper(fmt="iso"),
            structlog.processors.JSONRenderer(),
        ],
        wrapper_class=structlog.make_filtering_bound_logger(
            logging.getLevelNamesMapping()[settings().log_level]
        ),
    )
    provider = TracerProvider(resource=Resource.create({"service.name": service_name}))
    if settings().otlp_endpoint:
        provider.add_span_processor(BatchSpanProcessor(OTLPSpanExporter()))
    trace.set_tracer_provider(provider)


def logger(name: str) -> structlog.stdlib.BoundLogger:
    return structlog.get_logger(name)


def tracer(name: str) -> trace.Tracer:
    return trace.get_tracer(name)
