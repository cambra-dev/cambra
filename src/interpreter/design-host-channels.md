# Host channels

A host channel is a typed named port between a Cambra program and the program that embeds it. The
host declares its channels before compiling; a **source** becomes a call the program makes
(`price_updates()`), a **sink** becomes a feed the program writes (`cart_view << …`). Rows cross in
both directions as `Value`s.

The surface is `src/ccl/channels.rs`: `ChannelDecl`, `GlobalContext::register_channels`, and the
`Channels` handle a host pushes and drains through. The two runtime halves are
`src/interpreter/host_source.rs` and `src/interpreter/host_sink.rs`.

## Why not `http_serve`

`http_serve` is the other way data enters and leaves a program, and it cannot serve an embedded
host for two reasons.

It is a TCP listener. `SharedHttpServer` binds a port and spawns a dispatcher thread, so a host
with no sockets and no threads — a WebAssembly module — cannot use it at all.

Its bodies are strings. `HttpServerSharedState::process` accepts a `SealedFunction` whose codomain
is `Scalar(Strings)` and silently returns on any other shape, so a program serving a computed
number must render it first. There is no `Int → String` in CHL today, which made a rendering
builtin a prerequisite for serving any non-string value. A host sink takes the value as a value, so
the question does not arise.

`http_serve` remains the right surface for a program that is a server. A host channel is for a
program that is a component, and [Routes](#routes) is the shape a component serves an address in.

## The source

`HostSource` wraps `UIntStreamBuffer`, the same buffer `StdinDataSource` and `HttpServerDataSource`
hold. It mints a key per row as the row's arrival index, answers `retained_keys` with the rows no
producer has released, and drops a prefix once every registered producer agrees. `push` appends;
`close` says no more rows will arrive, which is what lets an aggregate over the stream converge.

**`TestDataSource` is not a substitute, and the difference is not cosmetic.** It holds a
`HashMap<Value, Value>` the caller keys itself, so a repeated key overwrites a row, arrival has no
order, and nothing is ever released. A program reading a live stream through it sees a window that
never advances, and a transactional read in a second loop lags the writes and then stalls — the
read stops tracking the store while the store keeps moving. Those are properties of the source, not
of the program: the same program over a `HostSource` reads the value that preceded each request
(`tests/compilation_pipeline/host_channels.rs`, "a_read_per_request_sees_the_price_that_preceded_it").
A source standing in for a stream has to have the stream's release semantics.

## The sink

`HostSink` is a `DataSink` whose `process` appends the tile's rows to an outbox the host drains.
Rows arrive in one of two shapes: row-shaped (`Scalar`, or the `Record` of columns a record-valued
feed produces) or a `SealedFunction` carrying one row per live domain key. A deleted position is a
row a filter rejected and never becomes a row.

`DataSink` carries no `Send`/`Sync` bound. Every sink is driven from the thread that owns the
operator graph; the HTTP sink hands work to its dispatcher thread and carries its own `Mutex` for
it, which is a property of that sink rather than of the trait.

## Binding a declared sink

A sink discovered during lowering brings its own binding. `http_serve` emits
`let responses = Defer in …` and registers the sink under that name, so `responses << x` is a feed
to a bound channel.

A host-declared sink has no statement to hang a binding on, so lowering wraps the whole program in
one `Defer` binding per declared name, outermost, and the feed lowers exactly as a response feed
does. Nothing else changes: the sink is still an out-of-band `(name, DataSink)` pair that
`compile_program` subscribes at the boundary, which is what `src/ccl/CLAUDE.md`, "Core invariant:
CCL is a pure value language" requires — `Defer` carries no behaviour.

A declared sink the program never feeds is rejected at lowering, as any unfed sink is.

## Routes

`wasm_serve(method, path)` binds a request/response pair of host channels registered under one
address. It is `http_serve`'s shape minus the port, and its arguments are compile-time constants as
`http_serve`'s are — an address is the identity of a route, decided while the program is still a
tree.

```python
cart_changes, cart_change_acks = wasm_serve("PATCH", "/cart")

for c in cart_changes:
    with begin():
        cart[(c.account, c.ticker)] := c.qty
        cart_change_acks << (ok=True, ticker=c.ticker, qty=c.qty)
```

The embedding page is the listener, so there is nothing to bind. The host declares both halves
before compiling, under the route spelled as a request line — `PATCH /cart`, which
`ccl::lower::wasm_route_name` mints:

```json
{ "name": "PATCH /cart", "kind": "request",  "type": "{account: Int, ticker: String, qty: Int}" },
{ "name": "PATCH /cart", "kind": "response", "type": "{ok: Bool, ticker: String, qty: Int}" }
```

A route is the one case where two declarations share a name, and the shared name is the pairing.
`register_channels` rejects a half-declared route: a request with no response is an address whose
callers never hear back, and a response with no request is a reply channel nothing can trigger.

Three things separate this from `http_serve`, none of them cosmetic.

**No transport is in it.** `http_serve` creates a `SharedHttpServer`, which binds a socket and
spawns a dispatcher thread, so it is a lowering error on a target that has neither. `wasm_serve`
creates nothing: both halves are host channels the host has already registered, and lowering looks
them up. That is what lets the construct exist on `wasm32`, and it is why the page rather than the
program decides how a call arrives.

**Rows cross as declared records.** `HttpServerSharedState::process` accepts a `SealedFunction`
whose codomain is `Scalar(Strings)` and silently returns on any other shape, so an HTTP program
renders its replies to strings. A route's request and reply are the record types their declarations
give them, so nothing in Cambra parses or renders a body.

**The address binds nothing.** `http_serve` mints a source name from the address and sanitises it
into an identifier; a route name is only ever a lookup key. `wasm_serve` binds the request source
and the reply sink to the two names its tuple target spells, and those names are what the program
reads and feeds. The reply sink is therefore declared through
`GlobalContext::declare_route_sink` rather than `declare_host_sink`: the latter wraps the whole
program in a `Defer` binding per declared name and rejects one nothing feeds, which would make
every address the host knows about an address this version has to serve.

A host drives a route through `Host::request(method, path, rows)`, and the reply leaves through the
route's sink — so it arrives in the `outputs` of the tick that computes it, under the route's name.
Correlation is arrival order, as it is for every host sink. A program that feeds no reply on some
path answers that call with nothing, and the host sees a call with no row rather than a wrong row;
that is a property of the program's shape, not of the route.

## Sockets

`wasm_socket_subscribe(endpoint, feed, products)` binds a host source whose rows arrive off a
socket, and records the subscription that fills it.

```python
ticker_updates = wasm_socket_subscribe(
    "wss://ws-feed.exchange.coinbase.com",
    "ticker_batch",
    ["BTC-USD", "ETH-USD", "SOL-USD"],
)

for u in ticker_updates:
    with begin():
        prices[u.ticker] := u.price
```

The source is declared like any other, and the statement binds it by the name it declares:

```json
{ "name": "ticker_updates", "kind": "source", "type": "{ticker: String, price: Int}" }
```

**No transport is in it**, for the reason [Routes](#routes) gives. The host owns the socket: the
browser's own `WebSocket` in a page, `tungstenite` in a native driver, a recorded slice replayed
offline. It connects, sends the subscription, decodes each message and pushes one typed row per
quote through `Host::push`. The rows cross as the record type the declaration gives them, so
**nothing in Cambra parses JSON or splits a string**. That is what lets the construct exist on
`wasm32`, where `tungstenite` cannot be built.

**It binds one name, not a pair.** A route binds the calls and the channel their replies leave by,
and destructures a 2-tuple to do it; a feed has nothing to reply to, so this is a plain `=` over a
single name. The recognition is the call rather than the target shape, so a tuple target is
answered by the rule it broke rather than by "the name is unbound".

**The arguments are not a lookup key.** A route is found by the address its call names; a
subscription's source is found by the name the statement binds, so its arguments would be checked
and thrown away if nothing carried them. They are the subscription: connect here, ask for this
feed, name these products. Lowering records them as a `SocketSubscription` the host reads back
through `Host::socket_subscriptions` — `Program.subscriptions()` in the WebAssembly wrapper —
before the first tick, which puts the endpoint in the program rather than in a page that has to be
kept in step with it.

They are compile-time constants for that reason rather than the one an address has. A host reads
them off the compiled program before it has ever ticked it, at which point no value in the program
exists to have computed one; a program that computed a subscription could not be connected until it
was already running, which is the wrong order for the only thing that fills it. The products are
therefore a list literal, since a comprehension over a constant list would have to be run during
lowering. An empty one is refused where it is written: a subscription that asks for nothing binds a
source the host can never fill, and every read of it waits forever on a feed behaving exactly as
written.

A product id is not a ticker. `"BTC-USD"` is an address at the exchange and `"BTC"` is a key in the
program, and the host decodes one into the other; the source's declared row type is the only thing
that says what arrives, and nothing requires the two vocabularies to agree.

The subscriptions are the one piece of registry state a version replaces rather than adds to. A
source, a listener and a declared sink outlive the version that named them, which is what carrying
state across a reload means. A subscription is a claim the running version makes about where its
rows come from, so a version that drops the feed has stopped making it, and the host closes the
socket it was holding.

## Row types

`ChannelDecl.row_type` is a CHL type expression, written the way a program would write it in an
annotation. `channels::parse_type` pairs `chl_parser::parse_expression` with `lower_type_expr`, and
`operator_conversion::ground_extent_of` derives the extent. The derivation is
`extent_of_resolving` with no source registry: a channel's row type is declared before anything is
compiled, so there is nothing to resolve a `Type::DataSource` against, and one appearing there is an
error rather than a lookup failure.

**Only an ingress channel needs an extent.** `HostSource` builds a column of arriving rows against
one, so a `source` or a `request` whose row type cannot be grounded is a row the buffer cannot hold.
`HostSink` takes a name and decodes whatever tiles the program hands it, so a `sink` or a
`response` declares a type and grounds nothing. The asymmetry is what lets a reply carry a list:
a list's extent names its length, a length is data, and a declaration has none to name — so
requiring one on the way out would reject exactly the rows the runtime can produce.

A `List(T)` crosses as a JSON array, in both directions. The runtime holds a list as a function over
`0..n` (`bindings_are_list`), so `row_from_json` mints the positions and `row_to_json` reads them
back off the bindings; order is the array's, and it is the whole content of a list. `row_to_json`
decides by the value rather than by a declared type, because a list and a map are one
`Value::Function` — a collection keyed by anything but its positions is a map, and says so rather
than encoding something a host cannot read. `Type::list_element` is the inverse of `Type::list_of`
and answers by the witness kind, which is `UIntRanges` for a list and `SubtypesOf(K)` for a map.

## Driving a program from a terminal

`src/host_driver.rs` is the host the binary supplies: rows arrive as JSON lines on stdin and leave
as JSON lines on stdout, one object per line.

```text
in   {"source": "price_updates", "rows": [{"ticker": "BTC-USD", "price": 8169291000000}]}
out  {"sink": "btc_line", "rows": [{"qty": 2, "price": 8169291000000, "total": 16338582000000}]}
```

The declarations travel beside the program as `channels.json` (`ChannelFile`), so `cambra
prog.cambra` runs, inspects and dumps a channel program from a path like any other — which is also
how the golden sweep reaches one.

Three properties the loop has, each of which the alternative gets wrong:

**One line is one host event.** The loop pushes at most one input line per tick. A program's answer
depends on what has already committed, so draining a backlog into one tick commits those rows
together, and a view request that followed a price in the input reads the value from before it.

**A malformed line is skipped, not fatal.** A host that sends one bad row has not stopped being a
host, and a driver that exits on it loses every row after it.

**End of input drains rather than stops.** A reader fires a tick or more after the write it reads,
so the loop runs on until the program has been quiet for a fixed number of ticks. A program reading
a socket has no end of input and keeps running.

Numbers cross as JSON, so an `Int` outside ±(2⁵³−1) is rejected at the boundary rather than
arriving rounded; scaled prices stay well inside it. A missing field, an extra field or a field of
the wrong type is an error — filling a default would put a value in the program the host never
sent, and ignoring an extra one would hide a host that believes it is sending something nothing
reads.

This is development plumbing. It exists so the app and the inspector can be built against `cargo
run` before the WebAssembly host is ready, and so a channel program in the gallery can be driven by
a subprocess test the way `streaming_echo` drives real stdin. A program with declared channels does
not also read `stdin()`: stdin is the channel transport for the length of the run.

## The embedding API

`src/embed.rs` is `Host`: compile a program against declared channels, push rows into its sources,
tick it, read what its sinks produced, and render a live frame. Nothing in it blocks, sleeps or
spawns — the host owns the clock — which is what lets the same type serve a terminal driver and a
WebAssembly module.

`Host::frame` calls `inspector_model::render_frame`, which is a pure function of the recorder and
the sources' windows. It lives in `inspector_model` rather than `inspector_server` for that reason:
the frame is wire, and only its delivery is transport, so a host with no socket renders the same
bytes the websocket route sends.

A recorder is installed at compile time or never. A producer takes its handle when its
`ProducerBase` is built, inside `compile_program`, and there is no traversal of the live graph to
hand one out afterwards.

**The binary's sink loop is a second copy of `Host::tick` and should become a call to it.** The two
were not merged in one step because `main.rs` also runs a pure program's `main` output to
convergence, which is a blocking run-to-completion shape rather than a tick, and unifying them means
`Host` handing that producer back. The `TODO` sits on the loop.

## The WebAssembly build

`ci.sh wasm` type-checks the library for `wasm32-unknown-unknown`. What it gates is that nothing has
re-entered the wasm build through an unguarded `use` — the module itself is produced by
`wasm-bindgen`, which is not a dependency of this repo.

Two crates are scoped to non-wasm targets in `Cargo.toml`: `tiny_http` (the inspector's server and
`http_serve`'s listener) and `tungstenite` (the live-values websocket). `tungstenite` cannot even be
*built* for wasm — it pulls `rand` and then `getrandom`, which refuses `wasm32-unknown-unknown`
unless a backend is chosen at link time.

They are scoped by target rather than behind a Cargo feature deliberately. A feature adds a standing
configuration every clippy pass has to cover, and it would let a native build turn the server off,
which nothing wants. A target table is not a build variant: it says these crates do not exist on
that platform, which is the fact.

`http_serve` is therefore a lowering error on wasm, where it names a source position, rather than a
bind that fails once the page has already loaded the module. **That arm is compile-checked by
`ci_wasm` and its message is exercised by no test** — a test for it would have to be gated to a
target the suite does not build, which is a test that cannot run.

`scripts/build-wasm.sh` builds the module and runs `scripts/wasm-contract.mjs` against it — the
same scenario `tests/embed.rs` runs natively, so a divergence is the wrapper's rather than the
program's. It needs `wasm-bindgen-cli` at the exact version the lock resolved, which the repo does
not depend on; `ci_wasm` runs it when it is present and reports the skip when it is not.

Measured on the demo program at the time of writing, in the `wasm-release` profile
(`opt-level = "z"`, LTO, stripped): **2.07 MB** module, **~160 ms** to compile the program in the
browser, **~116 ms per price row**. The recorded feed runs at 2.33 rows/s, so a row has ~430 ms and
the module uses about a quarter of it. Native release is ~22 ms per row, so wasm costs about five
times — more than the two-to-three a rough estimate would give, and worth re-measuring rather than
assuming. Size is traded for speed here: a `opt-level = "s"` or `"3"` module would be faster and
larger, and the budget has room either way.

`src/wasm_api.rs` is a thin wrapper over `Host`: every method converts JSON to and from the values
the embedding API already takes and adds nothing else. There is no run loop in it — the page owns
the clock — so a caller drives `tick` from whatever timer it likes and can stop without the module
holding a thread.

## Replay

Keys are minted from arrival order and nothing else, so a fresh source fed the same rows in the same
order holds the same keys, and a program compiled against the same declarations and fed the same
rows reaches the same state. A host that logs what it pushes can therefore rebuild a program's state
in a new process by replaying the log.

Replaying is for a restart, not for a new version of the source. A version swap is a reload
(`src/ccl/design/hot-reload.md`): `Host::reload` keeps every operator whose computation is unchanged
and resumes each mutable variable from the value it was holding, and the sources keep the rows they
already hold. Replaying a log into a reloaded program would deliver those rows a second time.
