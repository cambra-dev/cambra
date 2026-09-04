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
program that is a component.

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

## Row types

`ChannelDecl.row_type` is a CHL type expression, written the way a program would write it in an
annotation. `channels::parse_type` pairs `chl_parser::parse_expression` with `lower_type_expr`, and
`operator_conversion::ground_extent_of` derives the extent. The derivation is
`extent_of_resolving` with no source registry: a channel's row type is declared before anything is
compiled, so there is nothing to resolve a `Type::DataSource` against, and one appearing there is an
error rather than a lookup failure.

## Replay

Keys are minted from arrival order and nothing else, so a fresh source fed the same rows in the same
order holds the same keys, and a program compiled against the same declarations and fed the same
rows reaches the same state. A host that logs what it pushes can therefore rebuild a running
program's state in a new instance by replaying the log — which is how a host swaps a program for a
new version without any runtime support for carrying state across a recompile.
