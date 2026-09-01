"""Request and response bodies.

Every constraint the handlers rely on is stated here, so a malformed request is
refused at the boundary rather than in a handler: a negative quantity is a 422
from the framework, not an `if` in the domain code.
"""

from typing import Annotated, Literal

from pydantic import BaseModel, Field

Qty = Annotated[int, Field(ge=0)]
Sku = Annotated[str, Field(min_length=1, max_length=64)]
Identifier = Annotated[str, Field(min_length=1, max_length=64)]


class OrderRequest(BaseModel):
    sku: Sku
    qty: Qty


class OrderResponse(BaseModel):
    price: int
    discount: int


class RestockRequest(BaseModel):
    sku: Sku
    qty: Qty


class RestockResponse(BaseModel):
    sku: str
    qty: int


class StatsResponse(BaseModel):
    revenue: dict[str, int]


class CartRequest(BaseModel):
    sku: Sku
    qty: Qty


class CartResponse(BaseModel):
    id: str
    status: str


class CheckoutRequest(BaseModel):
    sku: Sku
    qty: Qty
    cart_id: Identifier | None = None
    # Test tokens, in the shape every payment processor uses: the stub service
    # fails `tok_fail` deterministically so the compensation path is reachable
    # from an integration test without fault injection in the application.
    payment_token: Literal["tok_ok", "tok_fail"] = "tok_ok"


class CheckoutResponse(BaseModel):
    id: str
    stage: str


class CheckoutStatus(BaseModel):
    id: str
    stage: str
    attempt: int
    detail: str | None


class DailyRevenueRow(BaseModel):
    day: str
    sku: str
    revenue: int
    units: int


class DailyRevenueResponse(BaseModel):
    rows: list[DailyRevenueRow]
