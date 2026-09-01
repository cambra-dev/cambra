"""Stand-ins for the three external services the saga calls.

Not part of the application: this is the local environment's substitute for a
payment processor, a warehouse API, and a transactional-email provider. It is
counted separately in `docs/REPORT.md` for that reason.

`tok_fail` is refused deterministically, which is how the integration test
reaches the compensation path without injecting faults into the application.
"""

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

app = FastAPI(title="External services (stub)")

_charges: dict[str, str] = {}
_shipments: dict[str, str] = {}


class Charge(BaseModel):
    idempotency_key: str
    amount: int
    token: str = "tok_ok"


class Void(BaseModel):
    auth_code: str


class Shipment(BaseModel):
    idempotency_key: str
    sku: str
    qty: int


class Mail(BaseModel):
    idempotency_key: str
    tracking: str


@app.post("/charges")
async def charge(body: Charge) -> dict[str, str]:
    if body.token == "tok_fail":
        raise HTTPException(status_code=402, detail="card declined")
    auth = _charges.setdefault(body.idempotency_key, f"auth_{body.idempotency_key[:12]}")
    return {"auth_code": auth}


@app.post("/voids")
async def void(body: Void) -> dict[str, str]:
    return {"status": "voided", "auth_code": body.auth_code}


@app.post("/shipments")
async def ship(body: Shipment) -> dict[str, str]:
    tracking = _shipments.setdefault(body.idempotency_key, f"trk_{body.idempotency_key[:12]}")
    return {"tracking": tracking}


@app.post("/send")
async def send(body: Mail) -> dict[str, str]:
    return {"status": "sent", "tracking": body.tracking}


@app.get("/health")
async def health() -> dict[str, str]:
    return {"status": "ok"}
