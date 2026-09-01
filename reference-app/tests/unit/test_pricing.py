"""The pricing contract, which is the Cambra program's `static assert` as tests.

The Cambra version states `p >= item.cost * qty` once inside `quote`, where it
lifts to a refinement on the return type and is discharged for every caller and
every future version. Here the same guarantee needs a case per shape, and the
cases only cover the shapes someone thought of.
"""

import pytest

from storefront.domain.errors import BelowCost
from storefront.domain.pricing import Item, promo_spent, quote

TEE = Item(sku="tee-black", price=25, cost=11)
POSTER = Item(sku="poster", price=10, cost=9)


def test_half_off_while_the_budget_lasts():
    assert quote(TEE, 2, promo_spent=False).price == 25


def test_list_price_once_the_budget_is_spent():
    assert quote(TEE, 2, promo_spent=True).price == 50


def test_discount_is_list_minus_paid():
    assert quote(TEE, 2, promo_spent=False).discount == 25


def test_cost_floor_clamps_a_low_margin_item():
    # Half off would be 5, below the cost of 9.
    assert quote(POSTER, 1, promo_spent=False).price == 9


def test_zero_quantity_is_free_and_still_above_cost():
    assert quote(TEE, 0, promo_spent=False).price == 0


@pytest.mark.parametrize("qty", [1, 2, 3, 7, 100])
@pytest.mark.parametrize("spent", [True, False])
@pytest.mark.parametrize("item", [TEE, POSTER])
def test_never_sells_below_cost(item: Item, qty: int, spent: bool):
    assert quote(item, qty, spent).price >= item.cost * qty


def test_below_cost_is_refused_rather_than_returned():
    """A catalog row priced under cost sells under cost once the sale ends.

    The list-price branch has no clamp — it does not need one for a well-formed
    catalog — so this is the shape the postcondition exists to catch. The
    database rejects such a row, and `Item` is constructible without it.
    """
    broken = Item(sku="broken", price=10, cost=100)
    with pytest.raises(BelowCost):
        quote(broken, 1, promo_spent=True)


def test_promo_spent_is_inclusive_of_the_budget():
    assert promo_spent(1000, 1000)
    assert not promo_spent(999, 1000)
