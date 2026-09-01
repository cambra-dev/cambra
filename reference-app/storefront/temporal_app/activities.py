"""The saga's steps. Everything that touches the world lives here.

Each activity is idempotent, because Temporal guarantees at-least-once execution
and a retried charge is a real one. Idempotency is by key: the payment service
takes an idempotency key, and every database write is keyed by checkout id.
"""

import httpx
from sqlalchemy import select
from temporalio import activity
from temporalio.exceptions import ApplicationError

from storefront.config import settings
from storefront.domain import inventory
from storefront.domain.errors import DomainError
from storefront.models import Cart, Checkout
from storefront.platform import db
from storefront.platform.observability import CHECKOUTS, EXTERNAL_CALLS, logger

log = logger(__name__)


async def _post(service: str, url: str, body: dict) -> dict:
    async with httpx.AsyncClient(timeout=5.0) as client:
        try:
            response = await client.post(url, json=body)
            response.raise_for_status()
        except httpx.HTTPStatusError as exc:
            EXTERNAL_CALLS.labels(service=service, outcome="rejected").inc()
            # A 4xx is the service's considered answer and will not change on a
            # retry; a 5xx or a timeout might, so only the first is terminal.
            raise ApplicationError(
                f"{service}: {exc.response.text}"[:200],
                non_retryable=400 <= exc.response.status_code < 500,
            ) from exc
        except httpx.HTTPError as exc:
            EXTERNAL_CALLS.labels(service=service, outcome="error").inc()
            raise ApplicationError(f"{service}: {exc}"[:200]) from exc
    EXTERNAL_CALLS.labels(service=service, outcome="ok").inc()
    return response.json()


@activity.defn
async def reserve_inventory(checkout_id: str, sku: str, qty: int) -> int:
    try:
        async with db.transaction() as s:
            item = await inventory.load_item(s, sku)
            await inventory.reserve(s, sku, qty)
            amount = item.price * qty
            row = await s.get(Checkout, checkout_id)
            row.amount = amount
            row.stage = "reserved"
    except DomainError as exc:
        # A 4xx-shaped failure: no stock will not become stock on a retry.
        raise ApplicationError(str(exc), non_retryable=True) from exc
    return amount


@activity.defn
async def release_inventory(sku: str, qty: int) -> None:
    async with db.transaction() as s:
        await inventory.release(s, sku, qty)


@activity.defn
async def authorize_payment(checkout_id: str, amount: int, payment_token: str) -> str:
    body = await _post(
        "payments",
        f"{settings().payments_url}/charges",
        {"idempotency_key": checkout_id, "amount": amount, "token": payment_token},
    )
    async with db.transaction() as s:
        row = await s.get(Checkout, checkout_id)
        if row is not None:
            row.stage = "authorized"
            row.detail = body["auth_code"]
    return body["auth_code"]


@activity.defn
async def void_authorization(auth_code: str) -> None:
    await _post("payments", f"{settings().payments_url}/voids", {"auth_code": auth_code})


@activity.defn
async def create_fulfilment(checkout_id: str, sku: str, qty: int) -> str:
    body = await _post(
        "warehouse",
        f"{settings().warehouse_url}/shipments",
        {"idempotency_key": checkout_id, "sku": sku, "qty": qty},
    )
    return body["tracking"]


@activity.defn
async def send_confirmation(checkout_id: str, tracking: str) -> None:
    await _post(
        "email",
        f"{settings().email_url}/send",
        {"idempotency_key": checkout_id, "tracking": tracking},
    )


@activity.defn
async def record_stage(checkout_id: str, stage: str, detail: str | None = None) -> None:
    async with db.transaction() as s:
        row = await s.get(Checkout, checkout_id)
        if row is not None:
            row.stage = stage
            row.detail = detail
    CHECKOUTS.labels(stage=stage).inc()
    log.info("checkout.stage", checkout_id=checkout_id, stage=stage)


@activity.defn
async def record_abandonment(cart_id: str) -> None:
    async with db.transaction() as s:
        row = await s.scalar(select(Cart).where(Cart.id == cart_id))
        if row is not None and row.status == "open":
            row.status = "abandoned"
    log.info("cart.abandoned", cart_id=cart_id)
