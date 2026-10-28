# Aspirational Cambra Sketches

Example programs for the workflow library, and a sketch of the std HTTP client. None compiles;
[workflow_library.md](../../../docs/libs/workflow_library.md) is the design. The library itself,
`std::wf` and its submodules with `std::retry`, `std::env` and `std::time`, is in
[std/](../../../std/README.md).

## The bill reminder

`bill-reminder.cambra` chases each tracked bill with a daily reminder until the bill is paid.

| Route | Effect |
| -- | -- |
| `POST /bills` | Starts the bill's run; tracking a bill twice starts nothing |
| `POST /bills/paid` | Completes the bill's run, which ends its reminders |
| `POST /bills/cancel` | Cancels the run named by its id, through the workflow's cancel route |

- `bills` is the workflow: one run per bill, with a 365-day timeout and a 30-day stale limit.
- `reminders` is a daily `std::wf::schedule` under `bills` with `on_due=`replace``: one run per bill
  per day, and a day still running when the next comes due is cancelled.
- The body, `send_for_reminder`, runs once per day's run. It looks up the bill's contact, composes a
  message for the contact's preferred channel, sends it as an SMS or an email, and completes the
  day's run once the send succeeds. A failed call leaves the run open until the next day replaces
  it.

## The bill reminder's versions

`bill-reminder-v1.cambra` to `bill-reminder-v4.cambra` are four versions of a simpler bill
reminder, each reloaded over the one before (`docs/libs/workflow_library.md`, "Example: the bill
reminder's versions"):

- v1 emails each bill daily.
- v2 adds an SMS every other day. Its `sms_body` passes the LLM's text through unbounded, so Twilio
  refuses a body over 1,600 characters and the SMS lands on `send_sms::failed`.
- v3 truncates the body, and resends each SMS v2's body broke, once, under the label `sms_fixed`,
  resolving each failure it resends.
- v4 drops v3's resend loop, and renames `sms_fixed` to `sms_resent` with `@RenamedFrom`, so a
  resend still in flight at the reload keeps its key.

## A schedule added by a reload

A schedule that a reload adds gives every parent run already live its first slot at the takeover
(`docs/libs/workflow_library.md`, "Schedules"). Every bill then starts a run in the same
instant, which is a burst of calls the size of the bill table. Two ways spread it:

- **Spread the first slot** (proposed): start each parent run's first slot at the takeover plus an
  offset hashed from its run id inside one period. The burst becomes one period of load, and a run's
  offset is the same on every reload. `std/wf/schedule.cambra` carries this as a TODO.
- **Anchor on the parent's start**: the first slot is the parent's start plus the first whole number
  of periods after the takeover, the slots the parent would have had under a schedule present from
  its start.

## Files

| File | Holds |
| -- | -- |
| `bill-reminder.cambra` | The bill reminder as a workflow body that calls effects as functions, `send_request(…)`, with exceptions for cancellation |
| `bill-reminder-v1.cambra` … `bill-reminder-v4.cambra` | The bill reminder's versions, each reloaded over the one before |
| `lib.cambra` | The bill reminder's providers: request and reply types, and a client constructor each for OpenAI, Resend and Twilio |
| `stdlib/http.cambra` | `http::http_client`, a sketch of the outbound half of `std::http` |
| `dynamic_sources.cambra` | Sources opened per runtime value: Kafka subscriptions as a `Txn` map, owned by workflow runs (`workflow_library.md`, "Data-configured sources") |
