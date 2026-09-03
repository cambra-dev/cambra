//! The websocket that carries a running program's recorded values to the pane.
//!
//! The static payload stays on `GET /api/snapshot`: a static lookup is
//! `span → node` and a live read is `(node, tick) → value`, so the two share no
//! index and keeping them on separate routes leaves the pinned snapshot
//! untouched (`src/inspector_model/design.md`).
//!
//! What crosses the socket is rendered rows, never a
//! [`Tile`](crate::interpreter::tiling::Tile). The
//! [`ValueRecorder`](crate::interpreter::value_recorder::ValueRecorder) renders
//! on the driver thread, which is what bounds its memory, so the only thing this
//! module moves between threads is a `String`.

use std::{
    collections::HashMap,
    io,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
        mpsc::{Receiver, Sender, channel},
    },
    thread,
};

use tiny_http::{ReadWrite, Request, Response, StatusCode};
use tungstenite::{
    Message, WebSocket, handshake::derive_accept_key, protocol::Role, protocol::WebSocketConfig,
};

#[cfg(test)]
use crate::interpreter::{ColumnValue, tiling::Tile};
use crate::{
    ccl::provenance::NodeId,
    interpreter::value_recorder::{RecordedRow, Recording, SharedRecorder, SourceWindow},
};
#[cfg(test)]
use std::{cell::RefCell, rc::Rc};

/// The route the pane connects to.
pub const LIVE_PATH: &str = "/api/live";

/// The newest frame, and a count of how many have been published.
///
/// Latest-wins rather than a queue: the driver spins at core speed whenever it
/// waits on external data, so a queue it fills every tick grows without bound
/// while a single cell does not. A reader wants current state, not every tick.
#[derive(Default)]
struct Latest {
    frame: Mutex<Option<String>>,
    published: AtomicU64,
}

/// A handle the driver publishes through.
#[derive(Clone)]
pub struct LiveChannel {
    latest: Arc<Latest>,
    wake: Sender<()>,
}

impl LiveChannel {
    /// Render the recorder's current state and hand it to the broadcaster.
    ///
    /// Called from the driver's per-tick hook, which sits between the pull and
    /// the release, so a source's retained window is sampled before anything is
    /// dropped from it.
    pub fn publish(&self, recorder: &SharedRecorder, sources: &[SourceWindow], tick: u64) {
        self.send(recorder, sources, tick, false);
    }

    /// Publish a last frame, marked `final`, and stop.
    ///
    /// Without it a converged run is indistinguishable from one that is merely
    /// idle: the process parks after the run so the socket stays open and
    /// simply goes quiet. A reader cannot infer "nothing more will ever arrive"
    /// from silence, so the run says so.
    pub fn finish(&self, recorder: &SharedRecorder, sources: &[SourceWindow], tick: u64) {
        self.send(recorder, sources, tick, true);
    }

    fn send(
        &self,
        recorder: &SharedRecorder,
        sources: &[SourceWindow],
        tick: u64,
        final_frame: bool,
    ) {
        let published = self.latest.published.fetch_add(1, Ordering::Release) + 1;
        let frame = render_frame(recorder, sources, tick, published, final_frame);
        *self.latest.frame.lock().expect("live frame lock") = Some(frame);
        // A full channel or a dead broadcaster must not stall the driver, so a
        // failed wake is dropped: the next publish wakes the same reader with
        // newer state anyway.
        let _ = self.wake.send(());
    }

    /// Frames published so far, for tests and for a client asking whether it is
    /// behind.
    pub fn published(&self) -> u64 {
        self.latest.published.load(Ordering::Acquire)
    }
}

/// The connections a broadcast writes to.
type Connections = Arc<Mutex<Vec<WebSocket<Box<dyn ReadWrite + Send>>>>>;

/// The live channel and the registry its broadcaster writes to.
pub struct LiveServer {
    channel: LiveChannel,
    connections: Connections,
}

impl LiveServer {
    /// Start the broadcaster and return the server.
    ///
    /// The broadcaster blocks on its wakeup channel, so it costs nothing while
    /// the program is idle — unlike the driver, which spins.
    pub fn start() -> Self {
        let (wake, woken) = channel();
        let latest = Arc::new(Latest::default());
        let connections: Connections = Arc::new(Mutex::new(Vec::new()));
        let server = Self {
            channel: LiveChannel {
                latest: Arc::clone(&latest),
                wake,
            },
            connections: Arc::clone(&connections),
        };
        thread::Builder::new()
            .name("cambra-live-broadcast".to_string())
            .spawn(move || broadcast_loop(&woken, &latest, &connections))
            .expect("spawning the live broadcaster");
        server
    }

    /// The handle to publish through.
    pub fn channel(&self) -> LiveChannel {
        self.channel.clone()
    }

    /// Answer a request on [`LIVE_PATH`] by taking its socket into the registry.
    ///
    /// A request carrying no `Sec-WebSocket-Key` is not an upgrade, and gets a
    /// 400 rather than being left hanging — a plain `GET /api/live` from a
    /// browser address bar reaches this.
    pub fn accept(&self, request: Request) -> io::Result<()> {
        let Some(key) = websocket_key(&request) else {
            return not_an_upgrade(request);
        };
        let accept = derive_accept_key(key.as_bytes());
        // `Response::add_header` silently drops `Connection`, `Upgrade`,
        // `Transfer-Encoding` and `Trailer`, and `upgrade` writes the first two
        // itself, so this sets only the one header that survives.
        let response = Response::empty(StatusCode(101)).with_header(
            format!("Sec-WebSocket-Accept: {accept}")
                .parse::<tiny_http::Header>()
                .expect("a derived accept key is a valid header value"),
        );
        let socket = request.upgrade("websocket", response);
        let mut websocket =
            WebSocket::from_raw_socket(socket, Role::Server, Some(WebSocketConfig::default()));
        // Hand the newcomer the current state rather than leaving it blank until
        // the next tick, which on a converged program never comes.
        if let Some(frame) = self
            .channel
            .latest
            .frame
            .lock()
            .expect("live frame lock")
            .clone()
            && let Err(e) = websocket.send(Message::Text(frame.into()))
        {
            log::debug!("live: a connection closed before its first frame: {e}");
            return Ok(());
        }
        self.connections
            .lock()
            .expect("live connections lock")
            .push(websocket);
        Ok(())
    }

    /// Frames published through this server's channel.
    pub fn published(&self) -> u64 {
        self.channel.published()
    }

    /// Connections currently held.
    pub fn connection_count(&self) -> usize {
        self.connections
            .lock()
            .expect("live connections lock")
            .len()
    }
}

/// Write each published frame to every connection, dropping the ones that fail.
fn broadcast_loop(woken: &Receiver<()>, latest: &Arc<Latest>, connections: &Connections) {
    while woken.recv().is_ok() {
        let Some(frame) = latest.frame.lock().expect("live frame lock").clone() else {
            continue;
        };
        // Collect under the lock and write after releasing it, so one slow
        // client cannot hold the lock the driver's next publish needs. The same
        // discipline `HttpServerSharedState` uses at its own I/O boundary.
        let mut held = std::mem::take(&mut *connections.lock().expect("live connections lock"));
        held.retain_mut(
            |socket| match socket.send(Message::Text(frame.clone().into())) {
                Ok(()) => true,
                Err(e) => {
                    log::debug!("live: dropping a connection: {e}");
                    false
                }
            },
        );
        let mut registry = connections.lock().expect("live connections lock");
        registry.append(&mut held);
    }
}

/// The `Sec-WebSocket-Key` header's value, if the request carries one.
fn websocket_key(request: &Request) -> Option<String> {
    request
        .headers()
        .iter()
        .find(|header| header.field.equiv("Sec-WebSocket-Key"))
        .map(|header| header.value.as_str().to_string())
}

/// The JSON a publish sends: one entry per producer that produced this tick.
///
/// Collapsed here rather than at recording time. A producer pulled twice in one
/// tick answers the second call empty, and another answers with the same tile
/// twice, so the newest recording is the wrong one to send and merging the two
/// double-counts — see
/// [`ValueRecorder::latest_non_empty`](crate::interpreter::value_recorder::ValueRecorder::latest_non_empty).
fn render_frame(
    recorder: &SharedRecorder,
    sources: &[SourceWindow],
    tick: u64,
    published: u64,
    final_frame: bool,
) -> String {
    let recorder = recorder.borrow();
    let mut by_node: HashMap<u64, Vec<serde_json::Value>> = HashMap::new();
    for (node_id, producer_id) in recorder.producers() {
        let Some(node) = node_id else { continue };
        let Some((recording, stale)) = recorder.latest_non_empty(node_id, producer_id) else {
            continue;
        };
        by_node
            .entry(node_key(node))
            .or_default()
            .push(producer_json(recording, stale));
    }
    let mut by_node: Vec<(u64, Vec<serde_json::Value>)> = by_node.into_iter().collect();
    // Ascending `NodeId`, which is both stable and meaningful: an operator's id
    // is minted when it is constructed, and construction is bottom-up, so a
    // smaller id sits further upstream. A `HashMap` iteration is neither —
    // unsorted, this array arrived in a different order on every run.
    by_node.sort_by_key(|(node, _)| *node);
    let nodes: Vec<serde_json::Value> = by_node
        .into_iter()
        .map(|(node, mut producers)| {
            // A node's producers are keyed by an allocation counter, so ordering
            // by it is stable across ticks; a `HashMap` iteration is not.
            producers.sort_by_key(|p| p["producerId"].as_u64().unwrap_or(0));
            serde_json::json!({ "nodeId": node, "producers": producers })
        })
        .collect();
    // `published` counts frames rather than ticks, so a client that reconnects
    // or misses a wake can tell it is behind. A producer's own `seq` is the
    // finer signal, for a gap within one node's recordings.
    // `final` says the run is over and this frame is the last. A reader that
    // never sees one and then loses the socket has been disconnected; a reader
    // holding one knows the quiet is the end rather than a pause.
    // A source ships beside the operators rather than among them: it has no
    // producer and takes no `get`, so it carries a window rather than a
    // recording, and a click on a source resolves to its own graph node.
    let sources: Vec<serde_json::Value> = sources
        .iter()
        .map(|window| {
            serde_json::json!({
                "nodeId": window.node_id.map(node_key),
                "name": window.name,
                "total": window.total,
                "dropped": window.dropped(),
                "rows": window.rows.iter().map(row_json).collect::<Vec<_>>(),
            })
        })
        .collect();
    serde_json::json!({
        "tick": tick,
        "published": published,
        "final": final_frame,
        "nodes": nodes,
        "sources": sources,
    })
    .to_string()
}

/// A `NodeId` as the number it ships as on the static wire.
fn node_key(node: NodeId) -> u64 {
    serde_json::to_value(node)
        .ok()
        .and_then(|value| value.as_u64())
        .unwrap_or_default()
}

/// One rendered row.
fn row_json(row: &RecordedRow) -> serde_json::Value {
    serde_json::json!({
        "key": row.key,
        "value": row.value,
        "deleted": row.deleted,
    })
}

/// One producer's rows.
fn producer_json(recording: &Recording, stale: bool) -> serde_json::Value {
    let rows: Vec<serde_json::Value> = recording.rows.iter().map(row_json).collect();
    serde_json::json!({
        "producerId": recording.producer_id,
        "producer": recording.producer,
        "shape": recording.shape,
        "watermark": recording.watermark,
        "note": recording.note,
        "tick": recording.tick,
        "seq": recording.seq,
        "stale": stale,
        "total": recording.total,
        "dropped": recording.dropped(),
        "rows": rows,
    })
}

/// A 400 for a request on the live path that is not an upgrade.
fn not_an_upgrade(request: Request) -> io::Result<()> {
    let body = b"the live route is a websocket upgrade";
    request.respond(Response::new(
        StatusCode(400),
        vec![
            "Content-Type: text/plain; charset=utf-8"
                .parse()
                .expect("static header parses"),
        ],
        &body[..],
        Some(body.len()),
        None,
    ))
}

#[cfg(test)]
mod tests {
    use std::{net::TcpStream, time::Duration};

    use crate::interpreter::value_recorder::{ValueRecorder, render_source_window};

    use super::*;

    /// Serve `live` on a loopback port until the test drops the returned port.
    ///
    /// A thread per test rather than a shared fixture, so two tests cannot see
    /// each other's connections.
    fn serve_live(live: Arc<LiveServer>) -> u16 {
        let server = tiny_http::Server::http("127.0.0.1:0").expect("binding a loopback port");
        let port = server.server_addr().to_ip().expect("an ip address").port();
        thread::spawn(move || {
            for request in server.incoming_requests() {
                let _ = live.accept(request);
            }
        });
        port
    }

    fn connect(port: u16) -> WebSocket<TcpStream> {
        let stream = TcpStream::connect(("127.0.0.1", port)).expect("connecting");
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .expect("a read timeout");
        let (socket, _) =
            tungstenite::client::client(format!("ws://127.0.0.1:{port}{LIVE_PATH}"), stream)
                .expect("the handshake completes");
        socket
    }

    fn recorder_with_one_row() -> SharedRecorder {
        let recorder = Rc::new(RefCell::new(ValueRecorder::with_defaults()));
        recorder.borrow_mut().set_tick(3);
        recorder.borrow_mut().record(
            Some(NodeId::fresh()),
            1,
            "MapResultWithSource#1",
            &Tile::Scalar(ColumnValue::Strings(vec!["hello".into()])),
        );
        recorder
    }

    fn read_frame(socket: &mut WebSocket<TcpStream>) -> serde_json::Value {
        loop {
            match socket.read().expect("reading a frame") {
                Message::Text(text) => {
                    return serde_json::from_str(&text).expect("a frame is JSON");
                }
                Message::Ping(_) | Message::Pong(_) => continue,
                other => panic!("expected text, got {other:?}"),
            }
        }
    }

    #[test]
    fn a_client_completes_the_handshake_and_is_registered() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let socket = connect(port);

        // The registry is written by the serving thread, so poll rather than
        // assume the push has landed.
        let mut registered = false;
        for _ in 0..100 {
            if live.connection_count() == 1 {
                registered = true;
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }
        assert!(registered, "the connection reaches the registry");
        drop(socket);
    }

    #[test]
    fn a_publish_reaches_a_connected_client() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 1 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        // The recorder is `!Send`, so it is built and published from a thread
        // that owns it — the driver's arrangement, in miniature.
        let channel = live.channel();
        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.publish(&recorder, &[], 3);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        assert_eq!(frame["tick"], 3);
        assert_eq!(frame["published"], 1);
        let rows = &frame["nodes"][0]["producers"][0]["rows"];
        assert_eq!(rows[0]["value"], "\"hello\"");
        assert_eq!(
            frame["nodes"][0]["producers"][0]["producer"],
            "MapResultWithSource#1"
        );
    }

    /// A client that connects after the last tick still sees state. A converged
    /// program publishes nothing further, so waiting for the next frame would
    /// wait forever.
    #[test]
    fn a_late_client_receives_the_current_frame_on_connect() {
        let live = Arc::new(LiveServer::start());
        let channel = live.channel();
        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.publish(&recorder, &[], 3);
        })
        .join()
        .expect("the publishing thread");

        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);
        let frame = read_frame(&mut socket);
        assert_eq!(frame["tick"], 3, "the frame published before connecting");
    }

    /// Unsorted, the node array arrived in a different order on every run, which
    /// would reshuffle the pane's groups and make a golden frame fixture flaky.
    #[test]
    fn a_frame_orders_its_nodes_by_id() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);

        let channel = live.channel();
        thread::spawn(move || {
            let recorder = Rc::new(RefCell::new(ValueRecorder::with_defaults()));
            // Recorded in an order that is not the id order, so a frame that
            // merely preserved insertion order would fail too.
            let ids: Vec<NodeId> = (0..6).map(|_| NodeId::fresh()).collect();
            for i in [3usize, 0, 5, 1, 4, 2] {
                recorder.borrow_mut().record(
                    Some(ids[i]),
                    i,
                    "P#1",
                    &Tile::Scalar(ColumnValue::Strings(vec!["v".into()])),
                );
            }
            channel.publish(&recorder, &[], 1);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        let order: Vec<u64> = frame["nodes"]
            .as_array()
            .expect("nodes is an array")
            .iter()
            .map(|n| n["nodeId"].as_u64().expect("a node id"))
            .collect();
        let mut ascending = order.clone();
        ascending.sort_unstable();
        assert_eq!(order, ascending, "nodes ship in ascending id order");
        assert_eq!(order.len(), 6);
    }

    #[test]
    fn a_frame_is_not_final_until_the_run_finishes() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 1 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        // Read between the two publishes. `Latest` is latest-wins, so a frame
        // may be coalesced away by the next one — asserting that both arrive
        // would contradict the property this transport is built on.
        let channel = live.channel();
        let publishing = channel.clone();
        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            publishing.publish(&recorder, &[], 3);
        })
        .join()
        .expect("the publishing thread");
        let running = read_frame(&mut socket);
        assert_eq!(running["final"], false, "a mid-run frame is not the last");

        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.finish(&recorder, &[], 4);
        })
        .join()
        .expect("the finishing thread");
        let last = read_frame(&mut socket);
        assert_eq!(last["final"], true, "the run says when it is over");
        assert_eq!(last["tick"], 4);
    }

    /// A reader that connects after the run is over still learns it is over,
    /// because the held frame is the final one.
    #[test]
    fn a_client_connecting_after_the_end_sees_the_final_frame() {
        let live = Arc::new(LiveServer::start());
        let channel = live.channel();
        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.finish(&recorder, &[], 9);
        })
        .join()
        .expect("the publishing thread");

        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);
        let frame = read_frame(&mut socket);
        assert_eq!(frame["final"], true);
        assert_eq!(frame["tick"], 9);
    }

    /// A source ships beside the operators, carrying a window rather than a
    /// recording: it has no producer and takes no `get`.
    #[test]
    fn a_frame_carries_a_source_window_beside_its_nodes() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);

        let node = NodeId::fresh();
        let window = render_source_window(
            Some(node),
            "stdin",
            &ColumnValue::from_uints(vec![0, 1]),
            &ColumnValue::Strings(vec!["a".into(), "b".into()]),
            8,
        );
        let channel = live.channel();
        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.publish(&recorder, &[window], 5);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        let sources = frame["sources"].as_array().expect("sources is an array");
        assert_eq!(sources.len(), 1);
        assert_eq!(sources[0]["name"], "stdin");
        assert_eq!(sources[0]["total"], 2);
        assert_eq!(sources[0]["rows"][1]["value"], "\"b\"");
        assert!(
            !frame["nodes"].as_array().expect("nodes").is_empty(),
            "operators still ship in the same frame"
        );
    }

    #[test]
    fn a_get_that_is_not_an_upgrade_is_refused() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(live);
        let mut stream = TcpStream::connect(("127.0.0.1", port)).expect("connecting");
        use std::io::{Read, Write};
        write!(
            stream,
            "GET {LIVE_PATH} HTTP/1.1\r\nHost: localhost\r\n\r\n"
        )
        .expect("writing a plain GET");
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .expect("a read timeout");
        // The status line only. Reading to EOF would wait out the timeout,
        // because the server keeps the connection alive after answering.
        let mut head = [0u8; 12];
        stream
            .read_exact(&mut head)
            .expect("reading the status line");
        assert_eq!(
            String::from_utf8_lossy(&head),
            "HTTP/1.1 400",
            "a plain GET is refused"
        );
    }
}
