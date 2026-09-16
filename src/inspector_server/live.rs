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
use crate::ccl::provenance::NodeId;
use crate::interpreter::value_recorder::{SharedRecorder, SourceWindow};
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
    /// Held together because a reader taking them separately could pair a frame
    /// with a later count: `send` bumps the count, renders, and only then
    /// stores, so a broadcaster waking in between would mark a connection as
    /// holding a frame it was never sent — and the real one is then skipped as
    /// already delivered, leaving that reader a frame behind for the rest of
    /// the run.
    frame: Mutex<Option<(String, u64)>>,
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
        let frame = crate::inspector_model::frame::render_frame(
            recorder,
            sources,
            tick,
            published,
            final_frame,
        );
        *self.latest.frame.lock().expect("live frame lock") = Some((frame, published));
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
/// A connection, and the `published` count of the last frame written to it.
///
/// The count is what makes delivery at-most-once per frame. `accept` wakes the
/// broadcaster so a newcomer is served without `accept` writing anything
/// itself, and that wake can be handled after a publish has already stored its
/// frame — so without a per-connection mark the same frame reaches an
/// established reader twice, and a reader that takes one frame per publish
/// falls a frame behind for the rest of the run.
struct Connection {
    socket: WebSocket<Box<dyn ReadWrite + Send>>,
    sent: u64,
}

type Connections = Arc<Mutex<Vec<Connection>>>;

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
        let websocket =
            WebSocket::from_raw_socket(socket, Role::Server, Some(WebSocketConfig::default()));
        // Register first, then ask the broadcaster for the current state, which
        // a newcomer needs because the next tick never comes on a converged
        // program. Writing it here instead cost two things. The frame lock would
        // be held across the write: `if let` holds the guard for the whole
        // let-chain, `send` is a blocking write-then-flush with no timeout, and
        // the lock a stalled client pins is the one `LiveChannel::send` takes on
        // the driver thread — so one client that never reads halts the
        // interpreter. And a publish landing between that write and this push
        // reached a socket the registry did not hold yet; latest-wins means it
        // was never resent, so a client could miss the `final` frame and sit on
        // a run that says more is coming.
        //
        // The wake costs every other connection a repeat of the frame it
        // already holds, which is a frame-shaped no-op: a frame is whole state.
        self.connections
            .lock()
            .expect("live connections lock")
            .push(Connection {
                socket: websocket,
                sent: 0,
            });
        let _ = self.channel.wake.send(());
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
        // Read the count under the same lock as the frame it belongs to, so a
        // connection's mark names the frame it actually received.
        let Some((frame, published)) = latest.frame.lock().expect("live frame lock").clone() else {
            continue;
        };
        // Collect under the lock and write after releasing it, so one slow
        // client cannot hold the lock the driver's next publish needs. The same
        // discipline `HttpServerSharedState` uses at its own I/O boundary.
        let mut held = std::mem::take(&mut *connections.lock().expect("live connections lock"));
        held.retain_mut(|conn| {
            if conn.sent >= published {
                return true;
            }
            match conn.socket.send(Message::Text(frame.clone().into())) {
                Ok(()) => {
                    conn.sent = published;
                    true
                }
                Err(e) => {
                    log::debug!("live: dropping a connection: {e}");
                    false
                }
            }
        });
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

    /// A newcomer's arrival does not re-deliver a frame an established reader
    /// already has.
    ///
    /// `accept` wakes the broadcaster rather than writing the held frame
    /// itself, and that wake is indistinguishable from a publish's. Without a
    /// per-connection mark the wake re-sends the current frame to everyone, so
    /// a reader taking one frame per publish reads a repeat and is a frame
    /// behind for the rest of the run.
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
            let recorder = recorder_with_one_row();
            publishing.publish(&recorder, &[], 1);
        })
        .join()
        .expect("the publishing thread");
        assert_eq!(read_frame(&mut first)["tick"], 1);

        // The second arrival wakes the broadcaster; the first reader is current.
        let _second = connect(port);
        for _ in 0..100 {
            if live.connection_count() == 2 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }

        thread::spawn(move || {
            let recorder = recorder_with_one_row();
            channel.publish(&recorder, &[], 2);
        })
        .join()
        .expect("the second publishing thread");

        // The next frame the first reader takes is the next one published, not
        // a repeat of the frame it already holds.
        assert_eq!(read_frame(&mut first)["tick"], 2);
    }

    /// A connection is in the registry before anything is written to it.
    ///
    /// `accept` used to send the held frame first and register afterwards, which
    /// cost two things. A publish landing in that window wrote to a registry the
    /// socket was not in yet, and latest-wins meant it was never resent — so a
    /// client could miss the `final` frame and sit forever on a run that says
    /// more is coming. And the send held the frame lock, which is the lock
    /// `LiveChannel::send` takes on the driver thread, so a client that never
    /// read could stall the interpreter.
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
            let recorder = recorder_with_one_row();
            channel.finish(&recorder, &[], 4);
        })
        .join()
        .expect("the publishing thread");

        let frame = read_frame(&mut socket);
        assert_eq!(frame["final"], true);
        assert_eq!(frame["tick"], 4);
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
