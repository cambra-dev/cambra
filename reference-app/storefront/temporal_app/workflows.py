"""The two durable processes.

Workflow code is replayed from history on every worker restart, so it may not do
anything the replay cannot reproduce: no I/O, no clock, no randomness. Every
such thing is an activity, which is why the saga below reads as orchestration
and nothing else.
"""

from dataclasses import dataclass, field
from datetime import timedelta

from temporalio import workflow
from temporalio.common import RetryPolicy
from temporalio.exceptions import ActivityError

with workflow.unsafe.imports_passed_through():
    from storefront.temporal_app import activities

# Each external step is retried with exponential backoff. Five attempts over
# roughly a minute: long enough to ride out a payment processor's blip, short
# enough that a customer is not left waiting on a dead one.
EXTERNAL = RetryPolicy(
    initial_interval=timedelta(seconds=1),
    backoff_coefficient=2.0,
    maximum_interval=timedelta(seconds=30),
    maximum_attempts=5,
)
# Compensation must not give up: a void that never runs leaves money authorized
# against an order that will not ship.
COMPENSATION = RetryPolicy(
    initial_interval=timedelta(seconds=1),
    backoff_coefficient=2.0,
    maximum_interval=timedelta(seconds=30),
)


@dataclass
class CheckoutInput:
    checkout_id: str
    sku: str
    qty: int
    payment_token: str


@dataclass
class CartInput:
    cart_id: str
    after_seconds: int


@dataclass
class Compensation:
    """A completed step and how to undo it, recorded as the saga advances."""

    activity: str
    args: list = field(default_factory=list)


@workflow.defn
class CheckoutWorkflow:
    def __init__(self) -> None:
        self._stage = "starting"

    @workflow.query
    def stage(self) -> str:
        return self._stage

    @workflow.run
    async def run(self, arg: CheckoutInput) -> str:
        undo: list[Compensation] = []
        try:
            amount = await workflow.execute_activity(
                activities.reserve_inventory,
                args=[arg.checkout_id, arg.sku, arg.qty],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=EXTERNAL,
            )
            undo.append(Compensation("release_inventory", [arg.sku, arg.qty]))
            self._stage = "reserved"

            auth = await workflow.execute_activity(
                activities.authorize_payment,
                args=[arg.checkout_id, amount, arg.payment_token],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=EXTERNAL,
            )
            undo.append(Compensation("void_authorization", [auth]))
            self._stage = "authorized"

            tracking = await workflow.execute_activity(
                activities.create_fulfilment,
                args=[arg.checkout_id, arg.sku, arg.qty],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=EXTERNAL,
            )
            self._stage = "fulfilled"

            # The confirmation is the last step, so its failure compensates
            # nothing: the order stands whether or not the mail went out.
            await workflow.execute_activity(
                activities.send_confirmation,
                args=[arg.checkout_id, tracking],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=EXTERNAL,
            )
            self._stage = "confirmed"
            await workflow.execute_activity(
                activities.record_stage,
                args=[arg.checkout_id, "confirmed", tracking],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=COMPENSATION,
            )
            return "confirmed"
        except ActivityError as exc:
            reason = str(exc.cause or exc)[:200]
            self._stage = "compensating"
            for step in reversed(undo):
                await workflow.execute_activity(
                    getattr(activities, step.activity),
                    args=step.args,
                    start_to_close_timeout=timedelta(seconds=10),
                    retry_policy=COMPENSATION,
                )
            await workflow.execute_activity(
                activities.record_stage,
                args=[arg.checkout_id, "compensated", reason],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=COMPENSATION,
            )
            self._stage = "compensated"
            return "compensated"


@workflow.defn
class CartAbandonmentWorkflow:
    def __init__(self) -> None:
        self._checked_out = False

    @workflow.signal
    def checked_out(self) -> None:
        self._checked_out = True

    @workflow.run
    async def run(self, arg: CartInput) -> str:
        # `wait_condition` with a timeout is the cancellable timer: whichever of
        # the signal and the deadline arrives first wins, and neither can race
        # the other because both are recorded in the same history.
        try:
            await workflow.wait_condition(
                lambda: self._checked_out,
                timeout=timedelta(seconds=arg.after_seconds),
            )
        except TimeoutError:
            await workflow.execute_activity(
                activities.record_abandonment,
                args=[arg.cart_id],
                start_to_close_timeout=timedelta(seconds=10),
                retry_policy=COMPENSATION,
            )
            return "abandoned"
        return "checked_out"
