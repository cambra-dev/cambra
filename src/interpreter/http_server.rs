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
        Arc, Mutex,
        mpsc::{self, Receiver, Sender},
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

/// Channel sender for a single `(method, path)` route.
///
/// Each item is either `Some((body, request))` for a matched incoming request
/// or `None` to signal server shutdown.
type RouteSender = Sender<Option<(SmolStr, tiny_http::Request)>>;

/// Routing table shared between the dispatcher thread and the [`SharedHttpServer`] handle.
// shared-state-ok: the I/O boundary, not the operator graph — side effects live
// at the edge, and no operator reads this.
type RouteMap = Arc<Mutex<HashMap<(String, String), RouteSender>>>;

/// A single `tiny_http::Server` shared by all `http_serve` calls on the same port.
///
/// Each `(method, path)` pair is registered as a route via [`register`](Self::register),
/// which returns a `Receiver` delivering matching requests.  Requests that do not match
/// any registered route receive an immediate 404.
///
/// The background dispatcher thread is spawned once on construction and runs until the
/// server is dropped.
pub struct SharedHttpServer {
    /// Routing table: `(method, path)` → sender half of each route's channel.
    ///
    /// Protected by a `Mutex` so that new routes can be registered after the
    /// dispatcher thread is already running.
    routes: RouteMap,
}

impl SharedHttpServer {
    /// Bind to `port` synchronously, then spawn the dispatcher background thread.
    ///
    /// Binding before the spawn means a port-in-use or permission error is
    /// returned immediately at construction rather than causing a silent hang
    /// after the program appears to start successfully.
    pub fn new(port: u16) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let server = Server::http(format!("0.0.0.0:{port}"))?;
        debug!("HTTP server listening on 0.0.0.0:{port}");

        let routes: RouteMap = Arc::new(Mutex::new(HashMap::new()));
        let routes_bg = routes.clone();

        thread::spawn(move || {
            loop {
                match server.recv() {
                    Ok(mut request) => {
                        let req_method = request.method().to_string();
                        let req_url = request.url().to_string();

                        // Look up the route while holding the lock briefly.
                        let sender = routes_bg
                            .lock()
                            .unwrap()
                            .get(&(req_method.clone(), req_url.clone()))
                            .cloned();

                        match sender {
                            Some(tx) => {
                                let mut body_bytes = Vec::new();
                                let _ = request.as_reader().read_to_end(&mut body_bytes);
                                let body = SmolStr::new(String::from_utf8_lossy(&body_bytes));
                                if tx.send(Some((body, request))).is_err() {
                                    debug!("HTTP route {req_method} {req_url}: receiver dropped");
                                }
                            }
                            None => {
                                let _ = request.respond(
                                    Response::from_string("Not Found").with_status_code(404),
                                );
                            }
                        }
                    }
                    Err(e) => {
                        debug!("SharedHttpServer recv error: {e}");
                        // Notify all registered routes of server shutdown.
                        let senders: Vec<_> = routes_bg.lock().unwrap().values().cloned().collect();
                        for tx in senders {
                            let _ = tx.send(None);
                        }
                        break;
                    }
                }
            }
        });

        Ok(Self { routes })
    }

    /// Register a new `(method, path)` route and return the `Receiver` for incoming requests.
    ///
    /// Requests matching this route will be sent on the returned channel.  A value of `None`
    /// signals server shutdown.
    pub fn register(
        &self,
        method: String,
        path: String,
    ) -> Receiver<Option<(SmolStr, tiny_http::Request)>> {
        let (tx, rx) = mpsc::channel();
        self.routes.lock().unwrap().insert((method, path), tx);
        rx
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
/// `tests/reserve_port.rs` pins: were it to lapse, this allocator would go back
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
    pending: Mutex<HashMap<usize, tiny_http::Request>>,
}

impl HttpServerSharedState {
    fn new() -> Self {
        Self {
            pending: Mutex::new(HashMap::new()),
        }
    }

    /// Store a new pending request at `idx`.
    fn insert(&self, idx: usize, request: tiny_http::Request) {
        self.pending.lock().unwrap().insert(idx, request);
    }
}

impl DataSink for HttpServerSharedState {
    /// Dispatch HTTP responses for all live `(UInt index, String body)` entries in `tile`.
    ///
    /// Collects `(request, body)` pairs from the pending map while holding the
    /// lock, then releases the lock and sends each response outside of it so that
    /// HTTP I/O does not block other threads waiting on the pending map.
    fn process(&self, tile: &Tile) {
        let Tile::SealedFunction {
            domain,
            codomain,
            deleted,
            ..
        } = tile
        else {
            debug!("HttpServerSharedState::process: expected SealedFunction tile, got {tile:?}");
            return;
        };
        let ColumnValue::UInts(indices) = domain else {
            debug!("HttpServerSharedState::process: expected UInt domain, got {domain:?}");
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

    /// Request bodies (and their `tiny_http::Request` handles) arriving from the
    /// background thread.  `None` signals server shutdown.
    receiver: Receiver<Option<(SmolStr, tiny_http::Request)>>,

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

    /// Drain any requests the background thread has queued.  Returns `true` if
    /// at least one new request (or server shutdown) was received.
    fn check_for_new_data(&mut self) -> bool {
        let mut got_data = false;
        loop {
            match self.receiver.try_recv() {
                Ok(Some((body, request))) => {
                    self.add(body, request);
                    got_data = true;
                }
                Ok(None) => {
                    debug!("HTTP server shut down");
                    self.buf.eof_reached = true;
                    got_data = true;
                    break;
                }
                Err(_) => break,
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

    fn output_value_extent(&self) -> Extent {
        Extent::Base(BaseType::String)
    }

    fn output_type(&self) -> Type {
        Type::Base(BaseType::String)
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        self.buf.release(producer, obsolete);
    }
}
