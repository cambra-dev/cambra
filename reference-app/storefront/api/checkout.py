"""Starting the checkout saga, and reading where it got to.

The handler starts a workflow and returns; the saga outlives the request, which
is the point. Status comes from the database rather than from a workflow query
so that a completed saga still answers after its history has been archived.
"""

import uuid

from fastapi import APIRouter, HTTPException
from temporalio.service import RPCError

from storefront.api.deps import Session, Temporal
from storefront.config import settings
from storefront.models import Cart, Checkout
from storefront.schemas import CheckoutRequest, CheckoutResponse, CheckoutStatus
from storefront.temporal_app.workflows import (
    CartAbandonmentWorkflow,
    CheckoutInput,
    CheckoutWorkflow,
)

router = APIRouter()


@router.post("/checkout", response_model=CheckoutResponse, status_code=202)
async def start_checkout(
    body: CheckoutRequest, s: Session, client: Temporal
) -> CheckoutResponse:
    checkout_id = uuid.uuid4().hex

    if body.cart_id is not None:
        cart = await s.get(Cart, body.cart_id)
        if cart is None:
            raise HTTPException(status_code=404, detail="no such cart")
        cart.status = "checked_out"
        await s.commit()
        # Cancel the abandonment timer. A cart whose workflow has already fired
        # is gone from the server, and that is not an error here — the timer
        # firing and the checkout landing are a race the customer resolved.
        try:
            handle = client.get_workflow_handle(f"cart-{body.cart_id}")
            await handle.signal(CartAbandonmentWorkflow.checked_out)
        except RPCError:
            pass

    # The row exists before the workflow does, so `GET /checkout/{id}` answers
    # immediately and a saga that fails at its first step still has somewhere to
    # record that it compensated.
    s.add(
        Checkout(
            id=checkout_id, sku=body.sku, qty=body.qty, amount=0, stage="starting"
        )
    )
    await s.commit()

    await client.start_workflow(
        CheckoutWorkflow.run,
        CheckoutInput(
            checkout_id=checkout_id,
            sku=body.sku,
            qty=body.qty,
            payment_token=body.payment_token,
        ),
        id=f"checkout-{checkout_id}",
        task_queue=settings().task_queue,
    )
    return CheckoutResponse(id=checkout_id, stage="starting")


@router.get("/checkout/{checkout_id}", response_model=CheckoutStatus)
async def checkout_status(checkout_id: str, s: Session) -> CheckoutStatus:
    row = await s.get(Checkout, checkout_id)
    if row is None:
        raise HTTPException(status_code=404, detail="no such checkout")
    return CheckoutStatus(
        id=row.id, stage=row.stage, attempt=row.attempt, detail=row.detail
    )
