"""Blocks until the stack answers, so `make up` returns a usable environment.

Checks the API, the Temporal worker's task queue, and the stub services. The
compose healthchecks cover the infrastructure; this covers the application on
top of it, which is what a test run actually needs.
"""

import asyncio
import sys

import httpx
from temporalio.api.workflowservice.v1 import GetSystemInfoRequest
from temporalio.client import Client
from temporalio.service import RPCError

from storefront.config import settings

TIMEOUT_SECONDS = 180.0


async def _http_ready(url: str) -> bool:
    try:
        async with httpx.AsyncClient(timeout=2.0) as client:
            return (await client.get(url)).status_code == 200
    except httpx.HTTPError:
        return False


async def _temporal_ready() -> bool:
    try:
        client = await Client.connect(
            settings().temporal_target, namespace=settings().temporal_namespace
        )
        await client.workflow_service.get_system_info(GetSystemInfoRequest())
    except (RPCError, RuntimeError, OSError):
        return False
    return True


async def main() -> int:
    deadline = asyncio.get_running_loop().time() + TIMEOUT_SECONDS
    checks = {
        "api": lambda: _http_ready("http://api:8080/health"),
        "payments": lambda: _http_ready("http://payments:8090/health"),
        "temporal": _temporal_ready,
    }
    pending = dict(checks)
    while pending and asyncio.get_running_loop().time() < deadline:
        for name, check in list(pending.items()):
            if await check():
                print(f"ready: {name}")
                del pending[name]
        if pending:
            await asyncio.sleep(2.0)
    if pending:
        print(f"not ready: {', '.join(pending)}", file=sys.stderr)
        return 1
    print("stack ready")
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
