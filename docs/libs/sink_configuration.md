# Sink Configuration

A sink's configuration sets how calls reach a remote: how many at once, in which order across keys,
how failures are retried, and which idempotency key the remote sees. Each setting belongs to one of
the layers that handle a call ([workflow_library.md](workflow_library.md), "Retry"):

| Layer | Example | Configured by |
| -- | -- | -- |
| Effect | `send_email` | `wf::EffectConfig`, the `config` argument of `run std::wf::effect(…)` |
| Client | `lib::resend` | the client constructor's arguments |
| Protocol client | `http::http_client` | the client, which builds it (`http::Config`) |

The effect runs every retry: attempts, backoff, deadlines, and the count of answered
failures it passes to the client as `Attempt.generation`. The client supplies its API's
classification of replies and builds the remote idempotency key, and keeps no state across writes.
Neither the client nor the protocol client retries.
The protocol client sends one request. `EffectConfig` holds only `policy` today
([std/wf.cambra](../../std/wf.cambra)).

## Settings

| Setting | Governs | Layer | Status |
| -- | -- | -- | -- |
| Parallelism | calls in flight at once, per effect | effect | TBD |
| Connection limit | requests open at once, per remote | none: [A layer per remote](#a-layer-per-remote) | TBD |
| Scheduling | fairness between keys and between runs, so one run's burst does not starve the rest | effect | TBD |
| Classification | which replies are retried, and whether each was answered | client, overridable by the effect | `ClientCtor.retry_logic`; `RetryConfig.retry_logic` overrides |
| Cancel classification | what the remote did with an attempt cancelled at a run's end | client | `ClientCtor.cancel_logic` |
| Backoff | attempts, wait between them, reply deadline (`retry::BackoffPolicy`, `RetryConfig.deadline`) | effect | In `EffectConfig.policy` |
| Call timeout | the whole call, from admission, across attempts | effect | `RetryConfig.call_timeout` |
| Retry budget | retries across calls during a remote's outage, as AWS SDKs' per-client token bucket, gRPC's per-server throttling, or Envoy's cap of retries at 20% of active requests. In an outage every call fails and retries on its own policy, so the load on the remote grows with the number of calls in flight while it is least able to answer | none: [A layer per remote](#a-layer-per-remote) | TBD |
| Remote idempotency key | the key the remote sees, built from the call key, `Attempt.generation`, and what keeps the client's keys apart from other effects' on one account | client | In each client (`lib::resend`, `key_prefix`) |
| Request timeout | how long one request waits for its reply | protocol client | `http::Config.timeout` |

## Constraints between layers

- **The effect's reply deadline outlasts the request timeout.** Otherwise the effect sends attempt
  2 while attempt 1's request still waits for its reply, and two writes of one call are in flight
  at once. Nothing checks this (`std/retry.cambra`, `deadline`).

## Cycles

Pacing is how the library limits a cycle between effects
([workflow_library.md](workflow_library.md), "Retry loops and cycles"). Parallelism and scheduling
bound the load a cycle puts on a remote until an operator cancels its run; they do not end the
cycle.

## Open

### A layer per remote

No layer holds state for a remote. Each effect builds its own client, and each client builds its
own protocol client, so a connection limit or a retry budget held by any of them bounds one
effect's calls, not every call to the remote.

**[Proposed]** — a remote layer holds it: a value declared once per remote and account, and
passed to the constructor of every client that calls that remote. It holds the settings that span
effects: the connection limit, the retry budget, and a circuit breaker if one is added. Envoy's
upstream cluster and the handler behind a named .NET `HttpClient` hold the same settings.

**[Open]** — whether the library adds the layer; whether it is a run, since it holds state; and
whether its retry budget survives a crash, since an effect's retries do and the systems above keep
their budgets in process memory.
