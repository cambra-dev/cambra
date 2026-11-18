//! HTTP server source and sink.
//!
//! [`SharedHttpServer`] owns the single `tiny_http::Server` for a given port and
//! routes incoming requests to the matching `(method, path)` subscriber channel.
//! Multiple HTTP routes on the same port share one server via
//! [`SharedHttpServer::register`].
//!
//! [`HttpServerDataSource`] accepts incoming HTTP requests on a background thread
//! and exposes them as a streaming [`DataSourceDomainExtentImpl`] with a `UInt`
//! domain and complete tuple values containing method, target, headers, and UTF-8
//! body. The embedded run module constructs nominal Request values from these
//! tuples. Each admitted request receives a monotonically increasing uint index.

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
use tiny_http::{Header, Response, Server};

use crate::ccl::Type;
use crate::interpreter::{
    BaseType, ColumnValue, DataSink, DataSourceDomainExtentImpl, Extent, FuncBinding, Value,
    stream_buffer::UIntStreamBuffer,
    tiling::{Predicate, Tile},
    tuple_field,
};

fn http_tuple<const N: usize>(values: [Value; N]) -> Value {
    Value::Record(
        values
            .into_iter()
            .enumerate()
            .map(|(n, v)| (tuple_field(n), v))
            .collect(),
    )
}

fn request_type() -> Type {
    let string = || Type::Base(BaseType::String);
    Type::Tuple(vec![
        string(),
        string(),
        Type::list_of(Type::Tuple(vec![string(), string()])),
        string(),
    ])
}

fn request_extent() -> Extent {
    let string = || Extent::Base(BaseType::String);
    let header = Extent::Record(HashMap::from([
        (tuple_field(0), string()),
        (tuple_field(1), string()),
    ]));
    Extent::Record(HashMap::from([
        (tuple_field(0), string()),
        (tuple_field(1), string()),
        (
            tuple_field(2),
            Extent::Function {
                domain: Box::new(Extent::Base(BaseType::UInt)),
                codomain: Box::new(header),
            },
        ),
        (tuple_field(3), string()),
    ]))
}

fn nominal_payload(value: &Value) -> &Value {
    let Value::Union { inner, .. } = value else {
        panic!("a nominal HTTP value carries its constructor, got {value:?}")
    };
    inner
}

fn tuple_part(value: &Value, n: usize) -> &Value {
    let Value::Record(fields) = value else {
        panic!("an HTTP constructor's arguments are a tuple, got {value:?}")
    };
    fields
        .get(&tuple_field(n))
        .expect("the HTTP constructor has every argument")
}

fn response_header(name: &str, value: &str) -> Result<Header, String> {
    // tiny_http checks ASCII encoding but permits CR/LF and caller-supplied framing lengths.
    let token = |b: u8| b.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&b);
    if name.is_empty() || !name.bytes().all(token) {
        return Err("invalid response header name".into());
    }
    if !value
        .bytes()
        .all(|b| b == b'\t' || (b' '..=b'~').contains(&b))
        || value.trim_matches([' ', '\t']) != value
    {
        return Err("invalid response header value".into());
    }
    if [
        "Content-Length",
        "Transfer-Encoding",
        "Connection",
        "Trailer",
        "Upgrade",
    ]
    .iter()
    .any(|reserved| name.eq_ignore_ascii_case(reserved))
    {
        return Err("response framing headers are managed by the HTTP transport".into());
    }
    Header::from_bytes(name.as_bytes(), value.as_bytes())
        .map_err(|_| "invalid response header".into())
}

fn decode_response(value: &Value) -> Result<(u16, Vec<Header>, String), String> {
    let payload = nominal_payload(value);
    let status = tuple_part(payload, 0).as_int();
    let status = u16::try_from(status)
        .ok()
        .filter(|s| (200..=599).contains(s))
        .ok_or("invalid final response status")?;
    let Value::Function(headers) = tuple_part(payload, 1) else {
        panic!("response headers are a list")
    };
    let headers = headers
        .iter()
        .map(|h| {
            let h = nominal_payload(&h.output);
            response_header(
                tuple_part(h, 0).as_string().as_str(),
                tuple_part(h, 1).as_string().as_str(),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if headers
        .iter()
        .filter(|h| h.field.equiv("Content-Type"))
        .count()
        > 1
    {
        return Err("a response has at most one Content-Type header".into());
    }
    Ok((
        status,
        headers,
        tuple_part(payload, 2).as_string().to_string(),
    ))
}

// ---------------------------------------------------------------------------
// Per-port shared server
// ---------------------------------------------------------------------------

/// What the dispatcher thread sends a route.
pub enum RouteMessage {
    /// A request for the route, with its body read off.
    Request(Value, Box<tiny_http::Request>),
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

/// A single `tiny_http::Server` shared by all HTTP routes on the same port.
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
                        let req_method = request.method().to_string();
                        let req_url = request.url().to_string();

                        // A target whose path is no URI path matches no route.
                        let Ok(path) = request_path(&req_url) else {
                            let _ = request.respond(
                                Response::from_string("invalid request target")
                                    .with_status_code(400),
                            );
                            continue;
                        };
                        // Look up the route while holding the lock briefly.
                        let sender = routes_bg
                            .lock()
                            .unwrap()
                            .senders
                            .get(&(req_method.clone(), path))
                            .cloned();

                        match sender {
                            Some(tx) => {
                                let mut body_bytes = Vec::new();
                                if request.as_reader().read_to_end(&mut body_bytes).is_err() {
                                    let _ = request.respond(
                                        Response::from_string("invalid request body")
                                            .with_status_code(400),
                                    );
                                    continue;
                                }
                                let Ok(body) = String::from_utf8(body_bytes) else {
                                    let _ = request.respond(
                                        Response::from_string("request body must be UTF-8")
                                            .with_status_code(400),
                                    );
                                    continue;
                                };
                                let headers = Value::Function(
                                    request
                                        .headers()
                                        .iter()
                                        .enumerate()
                                        .map(|(n, h)| FuncBinding {
                                            input: Value::UInt(n as u64),
                                            output: http_tuple([
                                                Value::String(h.field.to_string().into()),
                                                Value::String(h.value.as_str().into()),
                                            ]),
                                        })
                                        .collect(),
                                );
                                let value = http_tuple([
                                    Value::String(req_method.as_str().into()),
                                    Value::String(req_url.clone().into()),
                                    headers,
                                    Value::String(body.into()),
                                ]);
                                if tx
                                    .send(RouteMessage::Request(value, Box::new(request)))
                                    .is_err()
                                {
                                    debug!("HTTP route {req_method} {req_url}: receiver dropped");
                                }
                            }
                            None => respond_not_found(request),
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
        debug_assert_eq!(
            route_path(&path).as_deref(),
            Ok(path.as_str()),
            "a route registers its normalized path",
        );
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

/// An HTTP route a compilation named but did not open.
///
/// Lowering declares one for a route that a compilation names and does not open:
///
/// - A compile that answers a question
///   ([`Endpoints::Inherited`](crate::ccl::lower::Endpoints::Inherited)), such as rendering a
///   difference, throws its context away while a socket and a routing-table entry outlive it. Opening the route would bind a socket and register a route for a version nobody
///   installed, and the real compile would then fail to bind the port it took.
/// - The compile that precedes installing a version
///   ([`Endpoints::BindPort`](crate::ccl::lower::Endpoints::BindPort)) binds the route's port
///   and registers no route. A route it registered would outlive a refusal, with nothing reading
///   its channel.
/// - Checking a module alone runs nothing, and reads its requests' type off this source.
/// - A route whose address reads a `const` parameter has no address until a run gives it one. In
///   every compilation the module's chain reads its requests off this source, under a name minted
///   from the statement, and each run's copy is renamed to the route at the address the run gives
///   (`HttpRoute::at`, `src/ccl/lower/http.rs`).
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
        request_extent()
    }

    fn output_type(&self) -> Type {
        request_type()
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

/// Reserve a port for a test program's HTTP route, held against every other
/// concurrent test — thread or process — for the rest of this process's life.
///
/// **Test-only.** Built under `cfg(test)`, which the suite builds under.
///
/// The obvious allocator — bind `:0`, read the port the kernel assigned,
/// close — is unsound here, and flakily so.  Closing makes the port a *hint*
/// that nothing owns: the listener that will really own it is
/// [`SharedHttpServer::new`]'s, opened at the far end of `compile_program`, and
/// until then `bind(:0)` in a *concurrently running test binary* is free to hand
/// the very same port out again.  Both compiles then race to bind it and the
/// loser fails with `EADDRINUSE`, surfacing as a lowering error from
/// HTTP route.  Under `cargo test`, where the http test binaries run alongside
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
#[cfg(test)]
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

/// Why `method` cannot be an HTTP method, or `Ok` if it can: a method is a token
/// (RFC 9110, "5.6.2. Tokens"), and it is case-sensitive (RFC 9110, "9.1. Overview"), so
/// `GET` and `get` are two methods.
pub fn check_method(method: &str) -> Result<(), String> {
    let tchar = |c: char| c.is_ascii_alphanumeric() || "!#$%&'*+-.^_`|~".contains(c);
    if method.is_empty() || !method.chars().all(tchar) {
        return Err(format!(
            "an HTTP method is a non-empty token of letters, digits and `!#$%&'*+-.^_`|~`, got \
             {method:?}"
        ));
    }
    Ok(())
}

/// `path` in the normal form two equivalent paths share (RFC 3986, "6.2.2. Syntax-Based
/// Normalization"), or why it is no absolute URI path. A percent-encoded unreserved character
/// is decoded, every other percent-encoding takes uppercase hex digits, and `.` and `..`
/// segments are removed: `/a%62`, `/ab` and `/x/../ab` are one path. A trailing `/` is kept,
/// so `/ping` and `/ping/` are two paths.
pub fn route_path(path: &str) -> Result<String, String> {
    if !path.starts_with('/') {
        return Err(format!("an HTTP path begins with `/`, got {path:?}"));
    }
    let unreserved = |b: u8| b.is_ascii_alphanumeric() || b"-._~".contains(&b);
    let allowed = |b: u8| unreserved(b) || b"!$&'()*+,;=:@/".contains(&b);
    let bytes = path.as_bytes();
    let mut encoded = String::with_capacity(path.len());
    let mut at = 0;
    while at < bytes.len() {
        let b = bytes[at];
        if b == b'%' {
            let hex = bytes
                .get(at + 1..at + 3)
                .and_then(|h| std::str::from_utf8(h).ok())
                .and_then(|h| u8::from_str_radix(h, 16).ok())
                .ok_or_else(|| format!("`%` in an HTTP path begins two hex digits, in {path:?}"))?;
            if unreserved(hex) {
                encoded.push(char::from(hex));
            } else {
                encoded.push_str(&format!("%{hex:02X}"));
            }
            at += 3;
        } else if allowed(b) {
            encoded.push(char::from(b));
            at += 1;
        } else {
            return Err(format!(
                "an HTTP path holds letters, digits, `-._~!$&'()*+,;=:@/` and percent-encodings, \
                 and {path:?} holds {:?}",
                path[at..]
                    .chars()
                    .next()
                    .expect("a character at a byte boundary")
            ));
        }
    }
    Ok(remove_dot_segments(&encoded))
}

/// `path`, an absolute path, with its `.` and `..` segments resolved (RFC 3986, "5.2.4. Remove
/// Dot Segments"). A `..` above the root stays at the root.
fn remove_dot_segments(path: &str) -> String {
    let mut segments: Vec<&str> = Vec::new();
    let mut parts = path[1..].split('/').peekable();
    while let Some(segment) = parts.next() {
        let last = parts.peek().is_none();
        match segment {
            "." | ".." => {
                if segment == ".." {
                    segments.pop();
                }
                // A dot segment at the end names its directory, so the path keeps the `/`.
                if last {
                    segments.push("");
                }
            }
            _ => segments.push(segment),
        }
    }
    format!("/{}", segments.join("/"))
}

/// The normalized path of a request's target ([`route_path`]): the target before its query,
/// with the scheme and authority of an absolute-form target dropped (RFC 9112, "3.2.2.
/// absolute-form").
fn request_path(target: &str) -> Result<String, String> {
    let before_query = target.split('?').next().unwrap_or_default();
    let origin = match before_query.split_once("://") {
        Some((scheme, rest)) if !scheme.contains('/') => {
            rest.find('/').map_or("/", |slash| &rest[slash..])
        }
        _ => before_query,
    };
    route_path(origin)
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
    /// Dispatch complete nominal responses at the live request keys in `tile`.
    ///
    /// Collects request/response pairs from the pending map while holding the
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
        let Tile::Scalar(responses) = codomain.as_ref() else {
            panic!("a nominal HTTP response is a complete value column, got {codomain:?}");
        };
        assert_eq!(
            indices.len(),
            responses.len(),
            "one response value per request key"
        );
        let to_send: Vec<_> = {
            let mut pending = self.pending.lock().unwrap();
            indices
                .iter()
                .enumerate()
                .filter_map(|(row, idx)| {
                    if deleted.contains(row) {
                        return None;
                    }
                    pending
                        .remove(idx)
                        .map(|req| (req, decode_response(&responses.index_at(row))))
                })
                .collect()
        };
        for (request, response) in to_send {
            match response {
                Ok((status, headers, body)) => {
                    let mut response =
                        Response::from_data(body.into_bytes()).with_status_code(status);
                    for header in headers {
                        response.add_header(header);
                    }
                    if let Err(e) = request.respond(response) {
                        debug!("HTTP respond error: {e}");
                    }
                }
                Err(reason) => {
                    log::error!("invalid HTTP response: {reason}");
                    let _ = request.respond(
                        Response::from_string("invalid HTTP response").with_status_code(500),
                    );
                }
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
/// The domain is `UInt` (request indices 0, 1, 2, …). Each output is a complete
/// `(method, target, headers, body)` tuple.
pub struct HttpServerDataSource {
    /// Shared buffer, indexing, and predicate bookkeeping.
    buf: UIntStreamBuffer<Value>,

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

    /// Accept a new request: buffer its complete value and retain its handle for response dispatch.
    fn add(&mut self, body: Value, request: tiny_http::Request) {
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
    fn answer_in_flight(&mut self) {
        while let Ok(RouteMessage::Request(_, request)) = self.receiver.try_recv() {
            respond_not_found(*request);
        }
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
                    self.add(body, *request);
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
            ColumnValue::UInts(v) => ColumnValue::from_values(
                v.iter().map(|i| self.buf.get(*i)).cloned().collect(),
                &request_extent(),
            ),
            other => panic!("HttpServerDataSource::get expected UInt key, got {other:?}"),
        }
    }

    /// The requests still in flight, which is what the inspector renders as the
    /// route's live tail.
    fn retained_window(&self) -> Option<std::ops::Range<u64>> {
        Some(self.buf.retained_window())
    }

    fn output_value_extent(&self) -> Extent {
        request_extent()
    }

    fn output_type(&self) -> Type {
        request_type()
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
        io::{Read, Write},
        net::TcpStream,
        sync::mpsc::RecvTimeoutError,
        time::Duration,
    };

    use super::*;

    /// Equivalent spellings of a path share one normal form, and distinct paths keep distinct
    /// ones (RFC 3986, "6.2.2. Syntax-Based Normalization").
    #[test]
    fn a_path_takes_its_normal_form() {
        for (path, normal) in [
            ("/", "/"),
            ("/ping", "/ping"),
            ("/ping/", "/ping/"),
            ("/a%62", "/ab"),
            ("/a%7e%2f", "/a~%2F"),
            ("/a/./b", "/a/b"),
            ("/a/b/..", "/a/"),
            ("/../a", "/a"),
            ("/x/../ab/.", "/ab/"),
            ("/a//b", "/a//b"),
            ("/a%2E%2E/b", "/a../b"),
        ] {
            assert_eq!(route_path(path).as_deref(), Ok(normal), "{path}");
        }
        for path in [
            "",
            "ping",
            "/a b",
            "/caf\u{e9}",
            "/a%2",
            "/a%zz",
            "/a?q",
            "/a#f",
        ] {
            assert!(route_path(path).is_err(), "{path:?} is no path");
        }
    }

    /// A method is a case-sensitive token (RFC 9110, "9.1. Overview").
    #[test]
    fn a_method_is_a_token() {
        for method in ["GET", "get", "PATCH", "X-Custom.1"] {
            assert_eq!(check_method(method), Ok(()), "{method}");
        }
        for method in ["", "G ET", "GET\r\n", "GÉT", "(GET)"] {
            assert!(check_method(method).is_err(), "{method:?}");
        }
    }

    /// A request's target reaches its route by the path before its query, in normal form, and
    /// an absolute-form target by its path alone.
    #[test]
    fn a_request_target_names_its_path() {
        for (target, path) in [
            ("/a%62?x=%41", "/ab"),
            ("http://example.com/a/./b?q", "/a/b"),
            ("http://example.com", "/"),
        ] {
            assert_eq!(request_path(target).as_deref(), Ok(path), "{target}");
        }
        assert!(request_path("*").is_err());
    }

    #[test]
    fn response_headers_validate_wire_syntax_and_transport_ownership() {
        for (name, value) in [
            ("", "value"),
            ("X Bad", "value"),
            ("X:Bad", "value"),
            ("X-Test", "a\r\nX-Injected: yes"),
            ("X-Test", "a\0b"),
            ("X-Test", "a\x7fb"),
            ("X-Test", "λ"),
            ("X-Test", " leading"),
            ("X-Test", "trailing\t"),
            ("content-length", "0"),
            ("Transfer-Encoding", "chunked"),
            ("Connection", "close"),
            ("Trailer", "X-Later"),
            ("Upgrade", "websocket"),
        ] {
            assert!(response_header(name, value).is_err(), "{name:?}: {value:?}");
        }
        for (name, value) in [
            ("X-Test", ""),
            ("Set-Cookie", "a=b; Path=/"),
            ("X-Test", "a\tb"),
        ] {
            assert!(response_header(name, value).is_ok(), "{name:?}: {value:?}");
        }
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
