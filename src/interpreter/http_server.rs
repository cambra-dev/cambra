//! HTTP server source and sink.
//!
//! [`SharedHttpServer`] owns the single `tiny_http::Server` for a given port and
//! routes incoming requests to the matching `(method, path)` subscriber channel.
//! Multiple `http_serve` calls on the same port share one server via
//! [`SharedHttpServer::register`].
//!
//! [`HttpServerDataSource`] accepts incoming HTTP requests on a background thread
//! and exposes them as a streaming [`DataSourceDomainExtentImpl`] with a `UInt`
//! domain and `String` codomain (the request body).  Each request is assigned a
//! monotonically-increasing uint index.

use std::{
    collections::HashMap,
    sync::{
        Arc, Mutex, PoisonError,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Receiver, Sender, TryRecvError},
    },
    thread,
};

use log::debug;
use smol_str::SmolStr;
use tiny_http::{Header, Response, Server};

use crate::ccl::Type;
use crate::interpreter::{
    BaseType, ColumnValue, DataSink, DataSourceDomainExtentImpl, Extent,
    stream_buffer::UIntStreamBuffer,
    tiling::{Predicate, Tile},
};

// ---------------------------------------------------------------------------
// Per-port shared server
// ---------------------------------------------------------------------------

/// What the dispatcher thread sends a route.
pub enum RouteMessage {
    /// A request for the route, with its body read off.
    Request(SmolStr, tiny_http::Request),
    /// The dispatcher stopped for a reason other than the program releasing the port, so no
    /// request reaches the route again. Two causes stop it. tiny_http's accept thread exits on
    /// its first `accept` error and closes the listener. A panic on the dispatcher thread ends
    /// the dispatcher and leaves the listener open, with nothing reading its requests.
    Failed(String),
}

/// Channel sender for a single `(method, path)` route.
type RouteSender = Sender<RouteMessage>;

/// Routing table shared between the dispatcher thread and the [`SharedHttpServer`] handle.
// shared-state-ok: the I/O boundary, not the operator graph — side effects live
// at the edge, and no operator reads this.
type RouteMap = Arc<Mutex<RouteTable>>;

/// Each route's channel, and the dispatcher's failure once it has failed.
struct RouteTable {
    /// `(method, path)` → sender half of each route's channel.
    senders: HashMap<(String, String), RouteSender>,
    /// The reason the dispatcher sent its routes as [`RouteMessage::Failed`]. It sits under the
    /// lock that guards `senders`, so [`SharedHttpServer::register`] sends it to a route
    /// registered after the failure, which no request reaches either.
    failure: Option<String>,
}

/// A single `tiny_http::Server` shared by all `http_serve` calls on the same port.
///
/// Each `(method, path)` pair is registered as a route via [`register`](Self::register),
/// which returns a `Receiver` delivering matching requests.  Requests that do not match
/// any registered route receive an immediate 404.
///
/// The background dispatcher thread is spawned once on construction and runs until this
/// handle is dropped, which is what releases the port. A program serves a port for as
/// long as some version of it binds a route there; dropping the last handle closes the
/// socket rather than leaving the address answering 404 forever (see
/// [`SourceSinkRegistry`](crate::ccl::context::SourceSinkRegistry)).
pub struct SharedHttpServer {
    /// The routing table, behind a `Mutex` so that routes can be registered after the
    /// dispatcher thread is running.
    routes: RouteMap,

    /// The listener, shared with the dispatcher thread.
    ///
    /// Held here as well as there so that dropping this handle can end the thread: `unblock`
    /// makes its `recv` return an error. Moving the server into the thread alone would leave
    /// the port bound for the life of the process, since nothing else can reach it to stop the
    /// loop.
    server: Arc<Server>,

    /// Set by [`Drop`] before it unblocks the dispatcher. The dispatcher reads an error from
    /// `recv` with this set as the program releasing the port, and sends no route anything;
    /// any other error is a listener failure ([`RouteMessage::Failed`]).
    releasing: Arc<AtomicBool>,
}

impl SharedHttpServer {
    /// Bind to `port` synchronously, then spawn the dispatcher background thread.
    ///
    /// Binding before the spawn means a port-in-use or permission error is
    /// returned immediately at construction rather than causing a silent hang
    /// after the program appears to start successfully.
    pub fn new(port: u16) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let server = Arc::new(Server::http(format!("0.0.0.0:{port}"))?);
        debug!("HTTP server listening on 0.0.0.0:{port}");

        let routes: RouteMap = Arc::new(Mutex::new(RouteTable {
            senders: HashMap::new(),
            failure: None,
        }));
        let releasing = Arc::new(AtomicBool::new(false));
        let routes_bg = routes.clone();
        let server_bg = server.clone();
        let releasing_bg = releasing.clone();

        thread::spawn(move || {
            let server = server_bg;
            let _report = ReportPanic(routes_bg.clone());
            loop {
                match server.recv() {
                    Ok(mut request) => {
                        let address = (request.method().to_string(), request.url().to_string());
                        if !routes_bg.lock().unwrap().senders.contains_key(&address) {
                            respond_not_found(request);
                            continue;
                        }
                        // tiny_http hands over a request before its body has arrived when the
                        // body is chunked, over 1024 bytes, or sent with `Expect: 100-continue`
                        // (`tiny_http::request::new_request`), so this read can outlast the route.
                        let mut body_bytes = Vec::new();
                        let _ = request.as_reader().read_to_end(&mut body_bytes);
                        let body = SmolStr::new(String::from_utf8_lossy(&body_bytes));
                        // The second lookup and the send share one critical section with
                        // `unregister`, and retirement drains a route's channel after
                        // unregistering it. A request sent here is therefore in the channel the
                        // drain reads, and a request whose second lookup follows the unregister
                        // finds the address unregistered, or registered to a later route.
                        let (unrouted, undelivered) = {
                            let table = routes_bg.lock().unwrap();
                            match table.senders.get(&address) {
                                Some(tx) => {
                                    (None, tx.send(RouteMessage::Request(body, request)).err())
                                }
                                None => (Some(request), None),
                            }
                        };
                        // Both are answered outside the lock. An undelivered request answers
                        // tiny_http's 500 when it drops, and a write can wait on an earlier
                        // response on the same connection.
                        if let Some(request) = unrouted {
                            respond_not_found(request);
                        }
                        if undelivered.is_some() {
                            let (method, path) = &address;
                            debug!("HTTP route {method} {path}: receiver dropped");
                        }
                    }
                    // `unblock` from `Drop`. The registry drops the handle only once no route
                    // remains on the port (`release_unrouted_ports`) or with its whole context,
                    // so no source reads these channels.
                    Err(_) if releasing_bg.load(Ordering::Acquire) => break,
                    Err(e) => {
                        debug!("SharedHttpServer recv error: {e}");
                        fail_routes(
                            &routes_bg,
                            &format!("the listener on port {port} stopped accepting: {e}"),
                        );
                        break;
                    }
                }
            }
        });

        Ok(Self {
            routes,
            server,
            releasing,
        })
    }

    /// Register a new `(method, path)` route and return the `Receiver` for incoming requests.
    ///
    /// Each request matching the route arrives on the returned channel as a
    /// [`RouteMessage::Request`]. A route registered after the dispatcher failed receives that
    /// failure at once.
    pub fn register(&self, method: String, path: String) -> Receiver<RouteMessage> {
        let (tx, rx) = mpsc::channel();
        let mut table = self.routes.lock().unwrap();
        if let Some(reason) = &table.failure {
            let _ = tx.send(RouteMessage::Failed(reason.clone()));
        }
        let address = (method, path);
        debug_assert!(
            !table.senders.contains_key(&address),
            "`{} {}` is registered while a route holds it: an address is unregistered before it \
             is registered again, or the source of the route it replaces polls a channel with no \
             sender",
            address.0,
            address.1,
        );
        table.senders.insert(address, tx);
        rx
    }

    /// Stop dispatching `method path`, so requests to it get the dispatcher's
    /// 404 rather than being buffered for a reader that no longer exists.
    ///
    /// A route outlives the version of the program that opened it — the listener
    /// and its table entry are held by the source/sink registry, not by the
    /// operator graph — so a version that stops serving one has to say so.
    /// Without this the route still matches, still buffers, and the client waits
    /// on a reply nobody will compute.
    ///
    /// This drops the route's sender, and a poll of a channel with no sender panics. The caller
    /// stops the scheduler polling the route's source in the same step, as
    /// [`GlobalContext::retire_routes_absent_from`](crate::ccl::context::GlobalContext::retire_routes_absent_from)
    /// does.
    pub fn unregister(&self, method: &str, path: &str) {
        self.routes
            .lock()
            .unwrap()
            .senders
            .remove(&(method.to_string(), path.to_string()));
    }
}

/// An `http_serve` route a compilation named but did not open.
///
/// A compilation that installs no version lowers a route the program does not serve to this:
///
/// - Rendering a difference ([`Endpoints::Inherited`](crate::ccl::lower::Endpoints::Inherited))
///   answers a question, and its context is thrown away while a socket and a routing-table entry
///   are not. Opening the route would bind a socket and register a route for a version nobody
///   installed, and the real compile would then fail to bind the port it took.
/// - The compile that precedes installing a version
///   ([`Endpoints::BindPort`](crate::ccl::lower::Endpoints::BindPort)) binds the route's port
///   and registers no route. A route it registered would outlive a refusal, with nothing reading
///   its channel.
/// - Checking a module alone runs nothing, and reads its requests' type off this source.
///
/// It answers the type questions lowering and inference put to a source and nothing else, which
/// is all a compile that stops above operator conversion asks. Reaching a runtime method means one
/// escaped into an operator graph, so each is [`unreachable`].
pub struct UnopenedRoute {
    id: String,
}

impl UnopenedRoute {
    pub fn new(id: String) -> Self {
        Self { id }
    }
}

impl DataSourceDomainExtentImpl for UnopenedRoute {
    fn get_id(&self) -> &str {
        &self.id
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(BaseType::String)
    }

    fn output_type(&self) -> Type {
        Type::Base(BaseType::String)
    }

    fn check_for_new_data(&mut self) -> bool {
        unreachable!("`{}` was never opened, so nothing drives it", self.id)
    }

    fn get_yield_predicate(&self) -> Predicate {
        unreachable!("`{}` was never opened, so it yields nothing", self.id)
    }

    fn get_elements(&self, _producer: &str) -> ColumnValue {
        unreachable!("`{}` was never opened, so it holds no elements", self.id)
    }

    fn get(&self, _keys: ColumnValue) -> ColumnValue {
        unreachable!("`{}` was never opened, so it answers no key", self.id)
    }

    fn release(&mut self, _producer: &str, _obsolete: Predicate) {
        unreachable!(
            "`{}` was never opened, so nothing subscribed to it",
            self.id
        )
    }

    fn carry_release_to_new_producers(&mut self, _predecessor: &std::collections::HashSet<String>) {
        unreachable!(
            "`{}` was never opened, so it has no release to carry",
            self.id
        )
    }

    fn first_position_for_a_new_producer(&self) -> u64 {
        unreachable!("`{}` was never opened, so it offers no position", self.id)
    }

    fn retire_producer(&mut self, _producer: &str) {
        unreachable!(
            "`{}` was never opened, so nothing registered with it",
            self.id
        )
    }
}

/// The reply sink of an [`UnopenedRoute`]. Dispatching to it would mean a version
/// nobody installed answering a request.
pub struct UnopenedRouteSink;

impl DataSink for UnopenedRouteSink {
    fn process(&self, _tile: &Tile) {
        unreachable!("a route that was never opened has no client to answer");
    }
}

impl Drop for SharedHttpServer {
    fn drop(&mut self) {
        // Ends the dispatcher thread, which drops its `Arc<Server>` and so closes the listener.
        // `releasing` is set first, so the loop reads the error `unblock` makes `recv` return as
        // this release rather than as a listener failure.
        self.releasing.store(true, Ordering::Release);
        self.server.unblock();
    }
}

/// Record `reason` as the dispatcher's failure, and send it to every route in `routes` as
/// [`RouteMessage::Failed`].
///
/// Reads a poisoned table too: [`ReportPanic`] calls this while the dispatcher unwinds, and the
/// panic it reports may be the one that poisoned the lock.
fn fail_routes(routes: &RouteMap, reason: &str) {
    let mut table = routes.lock().unwrap_or_else(PoisonError::into_inner);
    table.failure = Some(reason.to_string());
    for tx in table.senders.values() {
        let _ = tx.send(RouteMessage::Failed(reason.to_string()));
    }
}

/// Reports a panic on the dispatcher thread to every route, as [`RouteMessage::Failed`].
///
/// The routing table holds every route's sender for as long as [`SharedHttpServer`] lives, so a
/// dispatcher that dies without reporting leaves each channel open and empty, and a source
/// polling it reads no request and no failure.
struct ReportPanic(RouteMap);

impl Drop for ReportPanic {
    fn drop(&mut self) {
        if thread::panicking() {
            fail_routes(&self.0, "the HTTP dispatcher thread panicked");
        }
    }
}

// ---------------------------------------------------------------------------
// Test port reservation
// ---------------------------------------------------------------------------

/// Reserve a port for a test program's `http_serve`, held against every other
/// concurrent test — thread or process — for the rest of this process's life.
///
/// **Test-only.** Shared through the default-off `test-helpers` feature so the
/// integration-test crates hold one implementation rather than a copy each.
///
/// The obvious allocator — bind `:0`, read the port the kernel assigned,
/// close — is unsound here, and flakily so.  Closing makes the port a *hint*
/// that nothing owns: the listener that will really own it is
/// [`SharedHttpServer::new`]'s, opened at the far end of `compile_program`, and
/// until then `bind(:0)` in a *concurrently running test binary* is free to hand
/// the very same port out again.  Both compiles then race to bind it and the
/// loser fails with `EADDRINUSE`, surfacing as a lowering error from
/// `http_serve`.  Under `cargo test`, where the http test binaries run alongside
/// each other, that is the whole of the observed flakiness (measured: 13
/// failures in 7200 allocations at 24-way concurrency, every one of them a port
/// two processes had been handed at once).
///
/// So the reservation has to be held by something that outlives the hint.  An
/// advisory lock on a per-port file does it: exclusive across processes,
/// released by the OS on exit, so a crashed run cannot permanently blacklist
/// a port the way a leftover lock *file* would.  Sequential allocation from
/// `BASE` is then collision-free by construction rather than by luck — the
/// lock, not chance, decides who gets a port.  The bind probe covers the one
/// thing the lock cannot: a *foreign* process already listening there.
///
/// The exclusion has to hold *within* a process too, since `cargo test` runs a
/// binary's tests as threads of one process.  It does because [`File::try_lock`]
/// locks the open file description (`flock`, not a per-process `fcntl` lock), so
/// the second `File::create` of the same path contends with the first exactly as
/// another process would.  That property is what
/// `tests/it/reserve_port.rs` pins: were it to lapse, this allocator would go back
/// to handing one port to two callers, and the flakiness would return unchanged.
#[cfg(any(test, feature = "test-helpers"))]
pub fn reserve_test_port() -> u16 {
    use std::{fs::File, net::TcpListener, sync::Mutex};

    /// Below the lowest `ip_local_port_range` floor in practice (32768 on
    /// Linux, higher on macOS and Windows) so the kernel's own allocator
    /// never draws from this band for outbound connections, and clear of the
    /// privileged range.
    const BASE: u16 = 20_000;
    const SPAN: u16 = 10_000;

    /// Every lock this process holds.  The reservation must outlive the call —
    /// the server binds later, inside `compile_program` — and a test has no
    /// scope to keep a guard in, so the locks live until the process exits.
    // shared-state-ok: port reservations for the test harness, held open for the
    // process's lifetime. Outside the operator graph entirely — no operator reads it.
    static RESERVED: Mutex<Vec<File>> = Mutex::new(Vec::new());

    let dir = std::env::temp_dir();
    let mut last_create_err = None;
    for candidate in BASE..BASE + SPAN {
        let lock = match File::create(dir.join(format!("cambra-test-port-{candidate}.lock"))) {
            Ok(lock) => lock,
            // Failing to *create* the lock file is not a port being in use, and
            // the causes are per-directory rather than per-port: a read-only or
            // full `TMPDIR`, a descriptor limit, or a shared `/tmp` whose lock
            // files belong to another user.  Each of those rejects all 10 000
            // candidates, so without the error the loop reports port exhaustion
            // and points the reader at concurrency limits instead.
            Err(e) => {
                last_create_err = Some(e);
                continue;
            }
        };
        if lock.try_lock().is_err() {
            continue;
        }
        // Probe the same wildcard address `Server::http` will bind, so a
        // listener on any interface — not just loopback — rules the port out.
        if TcpListener::bind(("0.0.0.0", candidate)).is_err() {
            continue;
        }
        RESERVED.lock().unwrap().push(lock);
        return candidate;
    }
    match last_create_err {
        Some(e) => panic!(
            "no test port available in {BASE}..{}: could not create a lock file in {}: {e}",
            BASE + SPAN,
            dir.display(),
        ),
        None => panic!(
            "no test port available in {BASE}..{}: every port is reserved or already bound",
            BASE + SPAN,
        ),
    }
}

// ---------------------------------------------------------------------------
// Shared state
// ---------------------------------------------------------------------------

/// State shared between [`HttpServerDataSource`] and the [`crate::interpreter::DataSink`] response dispatch.
///
/// Holds the live `tiny_http::Request` objects (one per pending request) until
/// the CCL program produces a response for them.
pub struct HttpServerSharedState {
    /// Map from request index to the still-open `tiny_http::Request`.
    // shared-state-ok: the external-world boundary, where side effects live by
    // design. It holds the *socket* a request arrived on, not a value the program
    // computed: the request's data reaches the sink as a tile like anything else,
    // and this is what the reply is finally written to.
    pending: Mutex<HashMap<u64, tiny_http::Request>>,
}

impl HttpServerSharedState {
    fn new() -> Self {
        Self {
            pending: Mutex::new(HashMap::new()),
        }
    }

    /// Store a new pending request at `idx`.
    fn insert(&self, idx: u64, request: tiny_http::Request) {
        self.pending.lock().unwrap().insert(idx, request);
    }

    /// Answer every request still waiting for a reply with the 404 the
    /// dispatcher gives an address it holds no route for.
    ///
    /// Collects under the lock and responds outside it, for the reason
    /// [`process`](Self::process) does.
    fn answer_not_found(&self) {
        let waiting: Vec<tiny_http::Request> = {
            let mut pending = self.pending.lock().unwrap();
            pending.drain().map(|(_, request)| request).collect()
        };
        for request in waiting {
            respond_not_found(request);
        }
    }
}

/// The one answer a request gets when no version will compute a reply for it.
///
/// Shared by the dispatcher's no-such-route path and by retirement, so a client
/// sees the same thing whether its request arrived before or after the route
/// went.
fn respond_not_found(request: tiny_http::Request) {
    let response = Response::from_string("Not Found").with_status_code(404);
    if let Err(e) = request.respond(response) {
        debug!("HTTP respond error: {e}");
    }
}

impl DataSink for HttpServerSharedState {
    /// Dispatch HTTP responses for all live `(UInt index, String body)` entries in `tile`.
    ///
    /// Collects `(request, body)` pairs from the pending map while holding the
    /// lock, then releases the lock and sends each response outside of it so that
    /// HTTP I/O does not block other threads waiting on the pending map.
    fn process(&self, tile: &Tile) {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = tile
        else {
            debug!("HttpServerSharedState::process: expected a collection, got {tile:?}");
            return;
        };
        let ColumnValue::UInts(indices) = domain else {
            debug!("HttpServerSharedState::process: expected UInt keys, got {domain:?}");
            return;
        };
        let Tile::Scalar(ColumnValue::Strings(responses)) = codomain.as_ref() else {
            debug!(
                "HttpServerSharedState::process: expected Scalar(Strings) codomain, got {codomain:?}"
            );
            return;
        };

        // Collect (request, body) while the lock is held.
        let to_send: Vec<_> = {
            let mut pending = self.pending.lock().unwrap();
            indices
                .iter()
                .zip(responses.iter())
                .enumerate()
                .filter_map(|(j, (idx, body))| {
                    if deleted.contains(j) {
                        return None;
                    }
                    pending.remove(idx).map(|req| (req, body.clone()))
                })
                .collect()
        };

        let content_type: Header = "Content-Type: text/html; charset=utf-8"
            .parse()
            .expect("static header is valid");
        for (request, body) in to_send {
            let response = Response::from_string(body.as_str()).with_header(content_type.clone());
            if let Err(e) = request.respond(response) {
                debug!("HTTP respond error: {e}");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Data source
// ---------------------------------------------------------------------------

/// Buffers and tracks incoming HTTP requests for a single method/path endpoint.
///
/// A background thread listens on the given port using `tiny_http`.  Requests
/// that match `method` and `path` have their body read and are forwarded via an
/// `mpsc` channel; non-matching requests receive an immediate 404.
///
/// The domain is `UInt` (request indices 0, 1, 2, …) and the output value type
/// is `String` (the request body).
pub struct HttpServerDataSource {
    /// Shared buffer, indexing, and predicate bookkeeping.
    buf: UIntStreamBuffer,

    /// Requests, with their `tiny_http::Request` handles, from the dispatcher thread, or the
    /// dispatcher's failure.
    receiver: Receiver<RouteMessage>,

    /// Shared state for routing responses back to clients.
    shared: Arc<HttpServerSharedState>,

    /// Unique name for this source instance, used by `get_id`.
    id: String,
}

impl HttpServerDataSource {
    /// Create a new HTTP server data source for requests matching `method` and `path`.
    ///
    /// Registers the route with the provided [`SharedHttpServer`] instead of
    /// spawning a new server.  `id` is the canonical source name (used by `get_id`).
    pub fn new(server: &SharedHttpServer, method: String, path: String, id: String) -> Self {
        let receiver = server.register(method, path);
        let shared = Arc::new(HttpServerSharedState::new());

        Self {
            buf: UIntStreamBuffer::new(),
            receiver,
            shared,
            id,
        }
    }

    /// Return the [`DataSink`] that dispatches HTTP responses for this source.
    pub fn sink(&self) -> Arc<dyn DataSink> {
        self.shared.clone()
    }

    /// Accept a new request: store its body in the buffer and its handle in shared state.
    fn add(&mut self, body: SmolStr, request: tiny_http::Request) {
        let idx = self.buf.ready_size;
        self.shared.insert(idx, request);
        self.buf.push(body);
    }
}

impl DataSourceDomainExtentImpl for HttpServerDataSource {
    fn get_id(&self) -> &str {
        &self.id
    }

    /// A request reaches a reply through two stages, and retirement can catch it
    /// in either: the dispatcher's channel, before this source has accepted it,
    /// and the shared pending map, after. Both are answered, so the stage a
    /// request happened to be at does not decide what its client sees.
    ///
    /// The route is unregistered before this runs, and the dispatcher sends a request only under
    /// the routing-table lock with the route registered, so nothing reaches the channel after
    /// this drain.
    fn answer_in_flight(&mut self) {
        while let Ok(RouteMessage::Request(_, request)) = self.receiver.try_recv() {
            respond_not_found(request);
        }
        debug_assert!(
            matches!(self.receiver.try_recv(), Err(TryRecvError::Disconnected)),
            "route `{}` still has a sender after its drain: it was drained before it was \
             unregistered, or something besides the routing table holds its sender",
            self.id,
        );
        self.shared.answer_not_found();
    }

    /// Drain the requests the dispatcher thread has queued. Returns `true` if at least one
    /// arrived.
    ///
    /// Panics when the dispatcher has failed or the route's channel has no sender. Either way no
    /// request reaches the route again, and the program has no way to go on serving it.
    fn check_for_new_data(&mut self) -> bool {
        let mut got_data = false;
        loop {
            match self.receiver.try_recv() {
                Ok(RouteMessage::Request(body, request)) => {
                    self.add(body, request);
                    got_data = true;
                }
                Ok(RouteMessage::Failed(reason)) => {
                    panic!("route `{}` receives no more requests: {reason}", self.id)
                }
                Err(TryRecvError::Empty) => break,
                // The routing table holds the sender until the route is unregistered, and
                // retirement forgets the route's source in the step that unregisters it.
                Err(TryRecvError::Disconnected) => panic!(
                    "route `{}` was polled after its sender was dropped: it was unregistered or \
                     replaced while its source was still registered with the scheduler",
                    self.id
                ),
            }
        }
        got_data
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.buf.get_yield_predicate()
    }

    fn get_elements(&self, producer: &str) -> ColumnValue {
        self.buf.get_elements(producer)
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn get(&self, key: ColumnValue) -> ColumnValue {
        match key {
            ColumnValue::UInts(v) => {
                ColumnValue::Strings(v.iter().map(|i| self.buf.get(*i)).cloned().collect())
            }
            other => panic!("HttpServerDataSource::get expected UInt key, got {other:?}"),
        }
    }

    /// The requests still in flight, which is what the inspector renders as the
    /// route's live tail.
    fn retained_window(&self) -> Option<std::ops::Range<u64>> {
        Some(self.buf.retained_window())
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(BaseType::String)
    }

    fn output_type(&self) -> Type {
        Type::Base(BaseType::String)
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        self.buf.release(producer, obsolete);
    }

    fn carry_release_to_new_producers(&mut self, predecessor: &std::collections::HashSet<String>) {
        self.buf.carry_release_to_new_producers(predecessor);
    }

    fn first_position_for_a_new_producer(&self) -> u64 {
        self.buf.first_index_for_a_new_producer()
    }

    fn retire_producer(&mut self, producer: &str) {
        self.buf.retire_producer(producer);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        io::{BufRead, BufReader, Read, Write},
        net::TcpStream,
        sync::mpsc::RecvTimeoutError,
        time::Duration,
    };

    use super::*;

    /// Send `POST /x` with `Expect: 100-continue` and a four-byte body, and answer the final
    /// response's body. The body is held back: `continued` fires on the `100 Continue` the
    /// dispatcher writes when it starts reading the body, and the body is sent once `release`
    /// fires.
    fn post_held_at_its_body(port: u16, continued: Sender<()>, release: Receiver<()>) -> String {
        let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
        stream
            .write_all(
                b"POST /x HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length: 4\r\n\
                  Expect: 100-continue\r\nConnection: close\r\n\r\n",
            )
            .unwrap();
        let mut response = BufReader::new(stream.try_clone().unwrap());
        let mut line = String::new();
        while line != "\r\n" {
            line.clear();
            let read = response.read_line(&mut line).unwrap();
            assert_ne!(read, 0, "the connection closed before `100 Continue`");
        }
        continued.send(()).unwrap();
        release.recv().unwrap();
        stream.write_all(b"body").unwrap();
        let mut rest = String::new();
        response.read_to_string(&mut rest).unwrap();
        let body = rest.rsplit_once("\r\n\r\n").map(|(_, body)| body);
        body.unwrap_or_default().to_string()
    }

    /// A source named `route` reading the channel `messages` were sent on, with no listener.
    fn source_reading(messages: Vec<RouteMessage>) -> HttpServerDataSource {
        let (sender, receiver) = mpsc::channel();
        for message in messages {
            let _ = sender.send(message);
        }
        HttpServerDataSource {
            buf: UIntStreamBuffer::new(),
            receiver,
            shared: Arc::new(HttpServerSharedState::new()),
            id: "route".to_string(),
        }
    }

    /// A poll that reads the dispatcher's failure panics rather than reading an empty channel.
    #[test]
    #[should_panic(expected = "route `route` receives no more requests: the listener stopped")]
    fn a_failed_dispatcher_panics_the_poll() {
        let mut source = source_reading(vec![RouteMessage::Failed(
            "the listener stopped".to_string(),
        )]);
        source.check_for_new_data();
    }

    /// A poll of a channel with no sender panics: its route was unregistered while the scheduler
    /// still held its source.
    #[test]
    #[should_panic(expected = "route `route` was polled after its sender was dropped")]
    fn a_poll_of_a_route_with_no_sender_panics() {
        source_reading(Vec::new()).check_for_new_data();
    }

    /// The dispatcher holds no sender for a route while it reads a request's body. A route
    /// unregistered during the read is disconnected at once, and the request is answered 404.
    #[test]
    fn a_route_unregistered_during_a_body_read_answers_404() {
        let port = reserve_test_port();
        let server = SharedHttpServer::new(port).expect("the reserved port binds");
        let requests = server.register("POST".to_string(), "/x".to_string());
        let (continued, body_started) = mpsc::channel();
        let (release, released) = mpsc::channel();
        let client = thread::spawn(move || post_held_at_its_body(port, continued, released));

        body_started
            .recv_timeout(Duration::from_secs(5))
            .expect("the dispatcher starts reading the body");
        server.unregister("POST", "/x");
        assert!(
            matches!(requests.try_recv(), Err(TryRecvError::Disconnected)),
            "the routing table held the route's only sender",
        );
        release.send(()).unwrap();
        assert_eq!(client.join().unwrap(), "Not Found");
    }

    /// A route registered after the dispatcher failed reads that failure, since no request
    /// reaches it either.
    #[test]
    fn a_route_registered_after_a_failure_reads_it() {
        let server = SharedHttpServer::new(reserve_test_port()).expect("the reserved port binds");
        fail_routes(&server.routes, "the listener stopped");
        let requests = server.register("GET".to_string(), "/x".to_string());
        assert!(
            matches!(
                requests.try_recv(),
                Ok(RouteMessage::Failed(reason)) if reason == "the listener stopped"
            ),
            "the failure is on the channel before any request could be",
        );
    }

    /// Releasing a port ends the dispatcher without a message to the routes on it.
    #[test]
    fn releasing_a_port_sends_its_routes_nothing() {
        let server = SharedHttpServer::new(reserve_test_port()).expect("the reserved port binds");
        let requests = server.register("GET".to_string(), "/x".to_string());
        drop(server);
        assert!(
            matches!(
                requests.recv_timeout(Duration::from_secs(5)),
                Err(RecvTimeoutError::Disconnected)
            ),
            "the dispatcher returns without sending, and the routing table's sender goes with it",
        );
    }

    /// A panic on the dispatcher thread reaches every route as a failure.
    ///
    /// Poisoning the routing table makes the dispatcher's next lookup panic.
    #[test]
    fn a_dispatcher_that_panics_fails_its_routes() {
        let port = reserve_test_port();
        let server = SharedHttpServer::new(port).expect("the reserved port binds");
        let requests = server.register("GET".to_string(), "/x".to_string());
        let routes = server.routes.clone();
        let _ = thread::spawn(move || {
            let _held = routes.lock().unwrap();
            panic!("poisoning the routing table");
        })
        .join();

        thread::spawn(move || {
            let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
            stream
                .write_all(b"GET /x HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n")
                .unwrap();
            let _ = stream.read_to_end(&mut Vec::new());
        });

        let failed = requests.recv_timeout(Duration::from_secs(5));
        assert!(
            matches!(
                &failed,
                Ok(RouteMessage::Failed(reason)) if reason == "the HTTP dispatcher thread panicked"
            ),
            "the route reads the panic as the dispatcher's failure",
        );
    }
}
