# HTTP Server Design

`std::http::serve` runs one HTTP route and connects its exact request domain to nominal response
values. `std::http` is an importable module containing shared nominal types and pure helpers.

## CHL surface

```python
import std::http
run std::http::serve(port="8080", method="POST", path="/echo") as server
server::respond([http::ok_text(req.body()) for req in server::requests])
```

Each run exports `Reqs`, the route's source-domain type, `requests: Reqs |=> http::Request`, and
`respond(values: Reqs |=> http::Response)`. The response definition covers exactly that domain.
A filtered domain, contribution-site-tagged domain, or another route's domain is rejected.
The module defines its private response Feed once with `<<=`. No writable place is exported.

Request and response bodies are UTF-8 Strings. Invalid UTF-8 request bodies receive 400 before
source admission. Request bodies are limited to 1 MiB; larger bodies receive 413 before admission
and consume no request-domain key. This fixed limit applies to Content-Length and chunked bodies.
Header lists preserve order and repeated names. Response status codes range
from 200 through 599. Binary bodies, streaming, informational responses, protocol upgrades, and
TLS are not implemented.

Response header names are HTTP tokens. Values contain visible ASCII, spaces, and internal tabs;
leading or trailing whitespace and control characters are rejected. The transport owns
Content-Length, Transfer-Encoding, Connection, Keep-Alive, TE, Proxy-Connection, Trailer, and
Upgrade; a response that supplies those fields receives 500. Repeated Content-Type fields are rejected. Other repeated headers,
such as Set-Cookie, retain their order. Field syntax follows
[RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html#name-field-values).

A 204 or 304 response has an empty body and omits Content-Length and Transfer-Encoding. A
nonempty body at either status receives 500. Other final statuses range from 200 through 599.

Checking a module alone verifies its type contracts with its parameters abstract. Response
completion, response-domain equality after feed assembly, and uniqueness of routes are checked
when the complete program is assembled from its root
([Checking a module on its own](../../docs/chl-spec.md#914-checking-a-module-on-its-own)). A module
may leave a response connection to a caller using its public writer API.

## How runtime configuration reaches the operators

The embedded `std::http::serve` module declares its route with three `@Builtin` declarations:
the key type `Reqs`, the request source `_requests`, and the response Feed `_responses`. The
compiler supplies an alias of the route's source-domain type, a `Source`, and a response `Defer`,
and reads the address off the module's String constant parameters `port`, `method` and `path`.
The response sink registration is stored outside the pure CCL tree. A diagnostic prints the key
type as the run reaches it, `server::Reqs`.

A module interface retains its route templates. Linking substitutes run arguments into source
names in expressions, exported aliases, annotations, and quoted predicates. A nested run may
retain a symbolic address over its enclosing module's constant parameters. A concrete root run
resolves it to the route's canonical source name. Checking a module uses unopened sources and
opens no sockets.

A concrete route registration creates or reuses a `SharedHttpServer` for the port. Binding is
synchronous, so an unavailable port is a lowering error. `HttpServerDataSource` is registered
under the route's source name; its `HttpServerSharedState` sink is registered separately.
Duplicate `(port, method, path)` registrations are lowering errors.

After the CCL pipeline, `convert_outputs_to_operators` compiles the sink expressions in a shared
scope. `compile_program` subscribes one `SinkConsumer` per sink. Shared upstream operators use
`Memo` and `FanOut`; sink dispatch is never an expression node.

## Component map

| Component | Responsibility |
|---|---|
| `ccl/lower/http.rs` | Declares and instantiates route source-domain types, sources, and sinks |
| `stdlib/src/std/http.cambra` | Shared nominal Header, Request, Response, and pure helpers |
| `stdlib/src/std/http/serve.cambra` | Converts raw source tuples to nominal requests and defines the response connection |
| `SharedHttpServer` | Owns one listener per port and dispatches requests by method and path |
| `HttpServerDataSource` | Buffers complete request values at monotonically increasing UInt keys |
| `HttpServerSharedState` | Matches response keys to pending HTTP requests and sends responses |
| `SinkConsumer` | Pulls response tiles and calls the boundary sink |

## Per-port server sharing

One `tiny_http::Server` is bound per TCP port. `SharedHttpServer::register(method, path)` adds a
route and returns its receiver. The dispatcher matches the method exactly, since methods are
case-sensitive ([RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html#name-overview)). It matches
the path before the query string in the normal form `route_path` gives
([RFC 3986](https://www.rfc-editor.org/rfc/rfc3986.html#section-6.2.2)): a percent-encoded
unreserved character is decoded, other percent-encodings take uppercase hex digits, and `.` and
`..` segments are removed. A trailing `/` is kept, so `/ping` and `/ping/` are two routes. An
absolute-form target matches by its path. A target whose path is no URI path receives 400, and
an unmatched request receives 404. The complete target, including its query string, remains
available through `Request.target()`.

A route's declared method must be a token, and its declared path an absolute URI path; linking
refuses any other. The route is keyed by its normalized path, so two runs that spell one path
differently serve one route, which is refused as a duplicate.

For a matched request, the dispatcher reads and validates the UTF-8 body before enqueueing it.
It rejects an oversized Content-Length before reading and otherwise reads at most 1 MiB plus one
byte to detect overflow. Body reads have no deadline, and tiny_http retains responsibility for
unread-body cleanup. A stalled upload can still block the port's dispatcher.
Its raw value is `(method, target, headers, body)`, where headers are a materialized list of
String pairs. The embedded module uses ordinary CHL constructors to build nominal Header and
Request values. Sources continue to return `ColumnValue`; collection-valued fields open through
[Materialized source values](design-operators.md#materialized-source-values).

## Request/response matching

`UIntStreamBuffer<Value>` assigns each admitted request a monotonically increasing key.
`HttpServerSharedState` retains the corresponding open HTTP request in its pending map.
The response function preserves those keys. A nominal Response carries its growing payload as a
union tile. The sink materializes rows only when their payloads, including header lists, are
complete. It returns the consumed region to `SinkConsumer`, which releases that region to the
producer. Incomplete rows remain available for later pulls.

The sink decodes the status, repeated headers, and body and removes the pending request before
sending it. An invalid response header receives 500. Compile-time domain coverage establishes
one response value per admitted key; it does not guarantee eventual availability of arbitrary
data dependencies used to compute that value.

The source retains each request value until all readers release its key. The shared stream buffer
reclaims only an unbroken released prefix. Later released regions remain recorded until the
prefix reaches them. Partial record or collection-field releases do not release the whole source
value; the source adapter projects accumulated releases through shared levels.

## Multi-endpoint programs

Each run has a separate request source-domain type and response definition. Runs on one port
share its listener. The nominal Request and Response types belong to the shared imported module,
so the same typed handler can serve several runs while each response connection retains its own
domain contract.

## Shutdown and completion

`SinkConsumer` signals `DoneNotifier` when its tile is terminal. An HTTP request source remains
open, so an HTTP-serving program does not complete while its routes remain active.

Dropping a `SharedHttpServer` sets `releasing` and unblocks its dispatcher. The dispatcher exits
without reporting a listener failure, and the listener closes. The registry releases the handle
when no route remains on that port or the entire context is dropped. Route retirement is described
in [A route a version stops serving is retired](../ccl/design/program-evolution.md#a-route-a-version-stops-serving-is-retired).

A poll panics if it receives `RouteMessage::Failed` or finds a channel with no sender. The former
means the listener or dispatcher failed. The latter means the scheduler retained a source after
its route was unregistered. `ReportPanic` reports dispatcher panics to every route, and the route
table records failures for routes registered later.

An outstanding runtime limitation is listener recovery: tiny_http 0.12 ends its accept thread on
an accept error. A reported failure ends the process, including other routes and the control port.
Recovery requires rebinding or an accept loop that retries transient errors.

The compiler checks [sink domain contracts](../ccl/design/lowering.md#sink-domain-contracts) after
Feed assembly, when every deferred channel domain is concrete. A partial Feed therefore receives
a compilation error before operator conversion.
