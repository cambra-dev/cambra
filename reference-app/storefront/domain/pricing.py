"""Pricing, and the two contracts on it.

`quote` is half off list while the promotion budget lasts and list price once it
is spent, clamped from below by the item's cost. The clamp is what keeps the
postcondition true on a low-margin item: half off "poster" (list 10, cost 9)
would be 5, which is below cost.

The postcondition is checked after the fact because nothing here can check it
before. The Cambra program states it as `static assert p >= item.cost * qty`
inside `quote`, which lifts to a refinement on the return type and is discharged
at compile time for every caller and every future version of the function.
"""

from dataclasses import dataclass

from storefront.domain.errors import BelowCost


@dataclass(frozen=True)
class Item:
    sku: str
    price: int
    cost: int


@dataclass(frozen=True)
class Quote:
    price: int
    discount: int


def quote(item: Item, qty: int, promo_spent: bool) -> Quote:
    list_price = item.price * qty
    floor = item.cost * qty
    price = list_price if promo_spent else max(list_price // 2, floor)
    if price < floor:
        raise BelowCost(f"{item.sku}: quoted {price} below cost {floor}")
    return Quote(price=price, discount=list_price - price)


def promo_spent(spend_to_date: int, budget: int) -> bool:
    return spend_to_date >= budget
