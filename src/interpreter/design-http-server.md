# HTTP Server Design

Runtime architecture for `http_serve` — the built-in that exposes an HTTP endpoint to a CCL program.

---

## CHL surface

```python
requests, responses = http_serve("8080", "GET", "/path")
for req in requests:
    responses << "Received " + req
```

`http_serve(port, method, path)` is a **compiler special form**, not a runtime function call.  All three arguments must be string literals known at compile time.  The compiler expands the two-binding assignment into a `Source`/`Defer` pair and registers the response `DataSink` out-of-band; nothing about `http_serve` appears in the operator graph at runtime.

Limitations (current):
- Only plain string request/response bodies; no headers, status codes, or streaming.
- `Content-Type` is always `text/html; charset=utf-8`.
- No TLS/HTTPS.
- Only top-level assignments are detected; `http_serve` in nested scopes is not supported.

---

## How runtime configuration reaches the operators

Lowering extracts the literal `(port, method, path)` at compile time and constructs the runtime objects immediately:

1. A `SharedHttpServer` is created (or reused) for the port and binds the TCP socket synchronously — a bind failure becomes a `LoweringError` before any operator graph is built.
2. An `HttpServerDataSource` is registered as the `requests` source.
3. The `DataSink` (`HttpServerSharedState`) is stored in `LoweringContext::sink_bindings` keyed by the `responses` binding name.

The CCL AST carries **no representation of the configuration** — the rendezvous between the source/sink objects and the compiled operator graph is entirely through these registries.  This is why lowering must special-case `http_serve`: it needs the literal arguments at compile time to create the objects.

After the full CCL pipeline runs, `compile_program` calls `convert_record_fields_to_operators` on the join-planned `Let* Record{…}` tree.  This walks the `Let*` chain in a single pass, wrapping each binding once in `Memo`/`FanOut` and entering a shared scope, then compiles each `Record` field's expression in that shared scope to produce one operator per sink.  Every sink subgraph branches off the same memoised upstream operators — there is no duplication of shared computation across sinks.  The main program output becomes `Lit(Unit)`.

---

## Component map

```
lower.rs            HttpServerDataSource (source) + HttpServerSharedState (sink)
                    registered in LoweringContext before type inference

ccl/context.rs      compile_program extracts sink expressions post-pipeline,
                    subscribes SinkConsumer to each, returns SinksHandle

interpreter/
  http_server.rs    SharedHttpServer  — one tiny_http::Server per TCP port
                    HttpServerDataSource  — streams request bodies as UInt-indexed Strings
                    HttpServerSharedState — DataSink, holds open requests, sends responses

  sinks.rs          DoneNotifier  — atomic counter + channel, fires when all sinks finish
                    SinkConsumer  — Consumer impl, pulls tiles, calls DataSink::process
```

---

## Per-port server sharing

One `tiny_http::Server` is bound per TCP port, shared by all `http_serve` routes on that port.  `SharedHttpServer::mut_var(method, path)` adds a route and returns an `mpsc::Receiver` channel.  The background dispatcher reads each incoming request, looks up the route in the `RouteMap`, and either delivers the request body to the matching channel or returns 404.

Duplicate `(port, method, path)` registrations are rejected with a `LoweringError` at compile time.

The TCP socket is bound synchronously in `SharedHttpServer::new` (not inside the spawned thread) so that a port-in-use or permission error surfaces immediately as a compile-time error rather than a silent hang.

---

## Request/response matching

Each request is assigned a monotonically-increasing integer index by `UIntStreamBuffer`.  The CCL program iterates over that index domain.  `SinkConsumer` pulls tiles from the responses producer and calls `HttpServerSharedState::process`, which matches `(index, response-body)` pairs against the `pending` map and sends each HTTP response outside the lock.

`UIntStreamBuffer` drops a request body once every registered producer has released its index, which
bounds a long-lived server's memory to the requests still in flight. Bodies are dropped from the
front, so a release frees memory only over an unbroken run from the lowest index still held. A
release covering a later region is recorded and withheld from that producer; its memory is reclaimed
when the front is released.

---

## Multi-endpoint programs

Multiple `http_serve` calls each produce an independent `Source`/`Defer` pair and a separate entry in `LoweringContext::sink_bindings`.

---

## Shutdown and completion

`SinkConsumer` detects terminal tiles via `Tile::is_terminal()` and fires `DoneNotifier::signal()`.  `SinksHandle::done` fires once all consumers have signalled.  For long-lived HTTP servers the underlying `HttpServerDataSource` never reaches EOF, so `done` never fires; the scheduler loop in `main.rs` runs until the process is killed.

There is currently no graceful-shutdown mechanism for `SharedHttpServer`.
