//! The websocket that carries a running program's probe readings to the pane.
//!
//! The static payload stays on `GET /api/snapshot`: a static lookup is
//! `span → node` and a live read is `(node, tick) → value`, so the two share no
//! index and keeping them on separate routes leaves the pinned snapshot
//! untouched (`src/inspector_model/design.md`).
//!
//! What crosses the socket is rendered probe readings, never a
//! [`Tile`](crate::interpreter::tiling::Tile). The
//! [`ProbeTable`](crate::interpreter::value_probe::ProbeTable) renders
//! on the driver thread, which is what bounds its memory, so the only thing this
//! module moves between threads is a `String`.

use std::{
    io,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
        mpsc::{Receiver, SyncSender, TrySendError, sync_channel},
    },
    thread,
};

use tiny_http::{ReadWrite, Request, Response, StatusCode};
use tungstenite::{
    Message, WebSocket, handshake::derive_accept_key, protocol::Role, protocol::WebSocketConfig,
};

#[cfg(test)]
use crate::ccl::provenance::NodeId;
use crate::interpreter::value_probe::{SharedProbeTable, SourceWindow};
#[cfg(test)]
use crate::interpreter::{ColumnValue, tiling::Tile};
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
    /// The newest frame and the count it was published as, as one value.
    ///
    /// Held together because a writer taking them separately could pair a frame
    /// with a later count: `send` bumps the count, renders, and only then
    /// stores, so a writer waking in between would mark its connection as
    /// holding a frame it was never sent. The real one would then be skipped as
    /// already delivered, leaving that reader a frame behind for the rest of
    /// the run.
    frame: Mutex<Option<(String, u64)>>,
    published: AtomicU64,
}

/// The wake handle of every connection's writer thread.
///
/// Each channel has capacity one and is only ever `try_send`-ed, so a publish
/// never blocks on a connection. A full channel means a wake is already
/// pending, and the writer reads the newest frame when it takes it.
type Connections = Arc<Mutex<Vec<SyncSender<()>>>>;

/// A handle the driver publishes through.
#[derive(Clone)]
pub struct LiveChannel {
    latest: Arc<Latest>,
    connections: Connections,
}

impl LiveChannel {
    /// Render the probe table's current state and wake every connection's
    /// writer.
    pub fn publish_probes(&self, probes: &SharedProbeTable, sources: &[SourceWindow], tick: u64) {
        self.send(probes, sources, tick, false);
    }

    /// Publish a last probe frame, marked `final`, and stop.
    ///
    /// Without it a converged run is indistinguishable from one that is merely
    /// idle: the process parks after the run so the socket stays open and
    /// goes quiet. A reader cannot infer "nothing more will ever arrive" from
    /// silence, so the run says so.
    pub fn publish_final_probes(
        &self,
        probes: &SharedProbeTable,
        sources: &[SourceWindow],
        tick: u64,
    ) {
        self.send(probes, sources, tick, true);
    }

    fn send(
        &self,
        probes: &SharedProbeTable,
        sources: &[SourceWindow],
        tick: u64,
        final_frame: bool,
    ) {
        let published = self.latest.published.fetch_add(1, Ordering::Release) + 1;
        let frame = crate::inspector_model::frame::render_probe_frame(
            probes,
            sources,
            tick,
            published,
            final_frame,
        );
        *self.latest.frame.lock().expect("live frame lock") = Some((frame, published));
        wake_all(&self.connections);
    }

    /// Frames published so far, for tests and for a client asking whether it is
    /// behind.
    pub fn published(&self) -> u64 {
        self.latest.published.load(Ordering::Acquire)
    }
}

/// Wake every connection's writer, and forget the ones whose writer has
/// exited. Never blocks: the lock is held only across `try_send`s.
fn wake_all(connections: &Connections) {
    connections
        .lock()
        .expect("live connections lock")
        .retain(|wake| match wake.try_send(()) {
            Ok(()) | Err(TrySendError::Full(())) => true,
            Err(TrySendError::Disconnected(())) => false,
        });
}

/// The live channel and the connections it wakes.
pub struct LiveServer {
    channel: LiveChannel,
}

impl LiveServer {
    /// Create the server. It spawns nothing until a client connects.
    pub fn start() -> Self {
        Self {
            channel: LiveChannel {
                latest: Arc::new(Latest::default()),
                connections: Arc::new(Mutex::new(Vec::new())),
            },
        }
    }

    /// The handle to publish through.
    pub fn channel(&self) -> LiveChannel {
        self.channel.clone()
    }

    /// Answer a request on [`LIVE_PATH`] by upgrading it and starting a writer
    /// thread for the socket.
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
        let websocket =
            WebSocket::from_raw_socket(socket, Role::Server, Some(WebSocketConfig::default()));
        let (wake, woken) = sync_channel(1);
        let latest = Arc::clone(&self.channel.latest);
        thread::Builder::new()
            .name("cambra-live-writer".to_string())
            .spawn(move || write_loop(websocket, &woken, &latest))?;
        // Register, then wake the writer once itself. A newcomer needs the
        // current frame because the next publish never comes on a converged
        // program. Registering before that wake means a publish landing now
        // wakes the writer too, so the newest frame, including a `final` one,
        // always reaches it.
        let mut connections = self
            .channel
            .connections
            .lock()
            .expect("live connections lock");
        let _ = wake.try_send(());
        connections.push(wake);
        Ok(())
    }

    /// Frames published through this server's channel.
    pub fn published(&self) -> u64 {
        self.channel.published()
    }

    /// Connections whose writer has not been seen to exit.
    pub fn connection_count(&self) -> usize {
        self.channel
            .connections
            .lock()
            .expect("live connections lock")
            .len()
    }
}

/// Write the newest frame to one socket each time it is woken, until a write
/// fails or the server goes away.
///
/// One thread per connection, so a client that stops reading blocks only its
/// own writer. `sent` is the `published` count of the last frame written, which
/// makes delivery at-most-once per frame: a wake that finds no newer frame
/// writes nothing, so a reader taking one frame per publish never reads a
/// repeat and falls a frame behind.
fn write_loop(
    mut socket: WebSocket<Box<dyn ReadWrite + Send>>,
    woken: &Receiver<()>,
    latest: &Latest,
) {
    let mut sent = 0;
    while woken.recv().is_ok() {
        // The count is read under the same lock as the frame it belongs to, so
        // `sent` names the frame actually written.
        let Some((frame, published)) = latest.frame.lock().expect("live frame lock").clone() else {
            continue;
        };
        if published <= sent {
            continue;
        }
        if let Err(e) = socket.send(Message::Text(frame.into())) {
            log::debug!("live: dropping a connection: {e}");
            return;
        }
        sent = published;
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

    use crate::interpreter::value_probe::{ProbeTable, render_source_window};

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

    fn probes_with_one_row() -> SharedProbeTable {
        let probes = Rc::new(RefCell::new(ProbeTable::with_defaults()));
        probes.borrow_mut().set_tick(3);
        probes.borrow_mut().observe(
            Some(NodeId::fresh()),
            1,
            "MapResultWithSource#1",
            &Tile::Scalar(ColumnValue::Strings(vec!["hello".into()])),
        );
        probes
    }

    fn read_frame(socket: &mut WebSocket<TcpStream>) -> serde_json::Value {
        loop {
            match socket.read().expect("reading a frame") {
                Message::Text(text) => {
                    let frame = serde_json::from_str(&text).expect("a frame is JSON");
                    crate::inspector_server::wire_check::assert_probe_frame_shape(&frame);
                    return frame;
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

        // The probe table is `!Send`, so it is built and published from a thread
        // that owns it — the driver's arrangement, in miniature.
        let channel = live.channel();
        thread::spawn(move || {
            let probes = probes_with_one_row();
            channel.publish_probes(&probes, &[], 3);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        assert_eq!(frame["tick"], 3);
        assert_eq!(frame["published"], 1);
        let rows = &frame["nodes"][0]["probes"][0]["rows"];
        assert_eq!(rows[0]["value"], "\"hello\"");
        assert_eq!(
            frame["nodes"][0]["probes"][0]["producer"],
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
            let probes = probes_with_one_row();
            channel.publish_probes(&probes, &[], 3);
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
            let probes = Rc::new(RefCell::new(ProbeTable::with_defaults()));
            // Observed in an order that is not the id order, so a frame that
            // merely preserved insertion order would fail too.
            let ids: Vec<NodeId> = (0..6).map(|_| NodeId::fresh()).collect();
            for i in [3usize, 0, 5, 1, 4, 2] {
                probes.borrow_mut().observe(
                    Some(ids[i]),
                    i,
                    "P#1",
                    &Tile::Scalar(ColumnValue::Strings(vec!["v".into()])),
                );
            }
            channel.publish_probes(&probes, &[], 1);
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
            let probes = probes_with_one_row();
            publishing.publish_probes(&probes, &[], 3);
        })
        .join()
        .expect("the publishing thread");
        let running = read_frame(&mut socket);
        assert_eq!(running["final"], false, "a mid-run frame is not the last");

        thread::spawn(move || {
            let probes = probes_with_one_row();
            channel.publish_final_probes(&probes, &[], 4);
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
            let probes = probes_with_one_row();
            channel.publish_final_probes(&probes, &[], 9);
        })
        .join()
        .expect("the publishing thread");

        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);
        let frame = read_frame(&mut socket);
        assert_eq!(frame["final"], true);
        assert_eq!(frame["tick"], 9);
    }

    /// A newcomer's arrival does not re-deliver a frame an established reader
    /// already has.
    ///
    /// A writer woken with no newer frame writes nothing. Without that check,
    /// a wake that finds the frame the reader already holds re-sends it, and a
    /// reader taking one frame per publish reads a repeat and is a frame behind
    /// for the rest of the run.
    #[test]
    fn a_second_connection_does_not_re_deliver_the_frame_the_first_holds() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut first = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 1 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        let channel = live.channel();
        let publishing = channel.clone();
        thread::spawn(move || {
            let probes = probes_with_one_row();
            publishing.publish_probes(&probes, &[], 1);
        })
        .join()
        .expect("the publishing thread");
        assert_eq!(read_frame(&mut first)["tick"], 1);

        // The second arrival is served its own frame; the first reader is current.
        let _second = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 2 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        thread::spawn(move || {
            let probes = probes_with_one_row();
            channel.publish_probes(&probes, &[], 2);
        })
        .join()
        .expect("the second publishing thread");

        // The next frame the first reader takes is the next one published, not
        // a repeat of the frame it already holds.
        assert_eq!(read_frame(&mut first)["tick"], 2);
    }

    /// A connection is registered before anything is written to it, so a
    /// publish that lands while it connects still wakes its writer. Latest-wins
    /// never resends a frame, so a connection registered after a publish could
    /// miss the `final` frame and sit on a run that says more is coming.
    #[test]
    fn a_connection_is_registered_before_any_frame_is_written_to_it() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));

        // Nothing has been published, so there is no frame to hand over; the
        // socket is registered all the same.
        let mut socket = connect(port);
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        while live.connection_count() == 0 && std::time::Instant::now() < deadline {
            thread::yield_now();
        }
        assert_eq!(live.connection_count(), 1, "registered before any write");

        // The first frame it ever sees is the one published after it registered.
        let channel = live.channel();
        thread::spawn(move || {
            let probes = probes_with_one_row();
            channel.publish_final_probes(&probes, &[], 4);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        assert_eq!(frame["final"], true);
        assert_eq!(frame["tick"], 4);
    }

    /// A source ships beside the operators, carrying a window rather than a
    /// probe reading: it has no producer and takes no `get`.
    #[test]
    fn a_frame_carries_a_source_window_beside_its_nodes() {
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let mut socket = connect(port);

        let node = NodeId::fresh();
        let window = render_source_window(
            vec![node],
            "stdin",
            &ColumnValue::from_uints(vec![0, 1]),
            &ColumnValue::Strings(vec!["a".into(), "b".into()]),
            8,
        );
        let channel = live.channel();
        thread::spawn(move || {
            let probes = probes_with_one_row();
            channel.publish_probes(&probes, &[window], 5);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        let sources = frame["sources"].as_array().expect("sources is an array");
        assert_eq!(sources.len(), 1);
        assert_eq!(sources[0]["name"], "stdin");
        assert_eq!(sources[0]["total"], 2);
        assert_eq!(sources[0]["rows"][1]["value"], "\"b\"");
        assert_eq!(sources[0]["nodeIds"].as_array().map(Vec::len), Some(1));
        assert!(
            !frame["nodes"].as_array().expect("nodes").is_empty(),
            "operators still ship in the same frame"
        );
    }

    /// A client that stops reading blocks only its own writer. Each frame here
    /// is several megabytes, so the stalled socket's buffers fill within the
    /// first few, and a single writer serving every connection would stop
    /// there for all of them.
    #[test]
    fn a_client_that_stops_reading_does_not_stall_another() {
        const FRAMES: u64 = 6;
        let live = Arc::new(LiveServer::start());
        let port = serve_live(Arc::clone(&live));
        let _stalled = connect(port);
        let mut reader = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 2 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        let channel = live.channel();
        thread::spawn(move || {
            let probes = Rc::new(RefCell::new(ProbeTable::with_defaults()));
            let (node, big) = (NodeId::fresh(), "x".repeat(4 << 20));
            for tick in 1..=FRAMES {
                // One probe, re-read each tick, so every frame is one big row.
                probes.borrow_mut().observe(
                    Some(node),
                    1,
                    "P#1",
                    &Tile::Scalar(ColumnValue::Strings(vec![big.clone().into()])),
                );
                channel.publish_probes(&probes, &[], tick);
            }
        })
        .join()
        .expect("the publishing thread");

        let mut last = 0;
        while last < FRAMES {
            last = read_frame(&mut reader)["tick"].as_u64().expect("a tick");
        }
        assert_eq!(last, FRAMES, "the reading client reaches the last frame");
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
