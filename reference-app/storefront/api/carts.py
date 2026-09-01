"""Carts, and the abandonment timer each one starts.

Creating a cart starts a workflow whose only job is to wait. The wait is hours
long, so it cannot live in this process: a deploy in the meantime would drop
every pending cart on the floor.
"""

import uuid

from fastapi import APIRouter

from storefront.api.deps import Session, Temporal
from storefront.config import settings
from storefront.models import Cart
from storefront.schemas import CartRequest, CartResponse
from storefront.temporal_app.workflows import CartAbandonmentWorkflow, CartInput

router = APIRouter()


@router.post("/carts", response_model=CartResponse, status_code=201)
async def open_cart(body: CartRequest, s: Session, client: Temporal) -> CartResponse:
    cart_id = uuid.uuid4().hex
    s.add(Cart(id=cart_id, sku=body.sku, qty=body.qty, status="open"))
    await s.commit()

    await client.start_workflow(
        CartAbandonmentWorkflow.run,
        CartInput(cart_id=cart_id, after_seconds=settings().abandon_after_seconds),
        id=f"cart-{cart_id}",
        task_queue=settings().task_queue,
    )
    return CartResponse(id=cart_id, status="open")
