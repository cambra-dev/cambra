"""Domain failures the API layer maps to status codes."""


class DomainError(Exception):
    status_code = 400


class UnknownSku(DomainError):
    status_code = 404

    def __init__(self, sku: str) -> None:
        super().__init__(f"no such sku: {sku}")


class OutOfStock(DomainError):
    status_code = 409

    def __init__(self, sku: str) -> None:
        super().__init__(f"out of stock: {sku}")


class BelowCost(DomainError):
    """The pricing postcondition failed.

    In the Cambra program this is a `static assert` that no version of `quote`
    can violate. Here it can only be a runtime check, so it is one.
    """

    status_code = 500
