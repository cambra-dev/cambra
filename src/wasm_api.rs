//! The WebAssembly host's view of a program.
//!
//! A thin wrapper over [`Host`](crate::embed::Host): every method here converts
//! JSON to and from the values the embedding API already takes, and adds
//! nothing else. The contract a page programs against is
//! `src/interpreter/design-host-channels.md`, and the scenario it has to satisfy
//! is `tests/embed.rs` — the same one the native driver satisfies.
//!
//! ```js
//! const program = Program.compile(source, channels);
//! program.push("price_updates", [{ ticker: "BTC-USD", price: 8169291000000 }]);
//! const { outputs, produced } = program.tick();
//! if (produced) inspector.frame(program.frame(false));
//!
//! const { generation, kept, bound } = JSON.parse(program.reload(edited));
//! ```
//!
//! There is no run loop in here. The page owns the clock: `tick` does one
//! scheduler pass and returns, so a caller can drive it from `setTimeout`, from
//! an animation frame, or as fast as rows arrive, and can stop driving it
//! without the module holding a thread.

use serde::Serialize;
use wasm_bindgen::prelude::*;

use crate::ccl::Type;
use crate::ccl::channels::{ChannelDecl, row_from_json, row_to_json};
use crate::ccl::context::{ReuseTally, render_errors};
use crate::embed::{EmbedError, Host};
use crate::interpreter::Value;

/// Route a Rust panic to the browser console rather than an opaque trap.
///
/// A panic in a WebAssembly module unwinds into an `unreachable`, which reaches
/// the page as "RuntimeError: unreachable executed" and names nothing. Call once
/// before anything else.
#[wasm_bindgen]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

/// A compiled program the page drives.
#[wasm_bindgen]
pub struct Program {
    host: Host,
}

/// Decode a JS array of row objects against `row_type`.
///
/// `channel` names the source or route in the rejection, which is the only
/// difference between the two ingress paths: a call's body and a pushed row
/// cross the boundary as the same declared record.
fn decode_rows(rows: JsValue, row_type: &Type, channel: &str) -> Result<Vec<Value>, JsValue> {
    let rows: Vec<serde_json::Value> = serde_wasm_bindgen::from_value(rows)
        .map_err(|e| JsValue::from_str(&format!("rows for '{channel}': {e}")))?;
    rows.iter()
        .map(|row| {
            row_from_json(row, row_type)
                .map_err(|e| JsValue::from_str(&format!("row for '{channel}': {e}")))
        })
        .collect()
}

#[wasm_bindgen]
impl Program {
    /// Compile `source` against `channels`, a JSON array of
    /// `{name, kind, type}` declarations.
    ///
    /// Throws with the rendered diagnostics rather than returning a status, so
    /// a caller that forgets to check gets an exception instead of a program
    /// that silently does nothing.
    pub fn compile(name: &str, source: &str, channels: JsValue) -> Result<Program, JsValue> {
        let declarations: Vec<ChannelDecl> = serde_wasm_bindgen::from_value(channels)
            .map_err(|e| JsValue::from_str(&format!("channel declarations: {e}")))?;
        let host = Host::compile(name, source, &declarations)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        Ok(Program { host })
    }

    /// Replace the running program with the version `source` describes, and
    /// report what it kept as `{"generation": n, "kept": k, "bound": b}`.
    ///
    /// The page swaps its edited source in without losing what the program is
    /// holding: every operator whose computation is unchanged keeps running, and
    /// every mutable variable resumes from the value it held. `kept` of `bound`
    /// counts the operators taken from the replaced version rather than built,
    /// which is the evidence for the rest. Re-deriving the state instead, by
    /// pushing a journal of rows into a second program, would keep none of them.
    ///
    /// `generation` is the version now running, counting from `0`. The same
    /// number rides `snapshot()`'s `meta.generation` and every `frame()`, which
    /// is how a reader holding panes from one version recognizes a frame naming
    /// nodes it has never seen: a rebuilt operator is minted a fresh `NodeId`,
    /// and re-reading the payload is what resolves it.
    ///
    /// A JSON string, as `snapshot()`, `frame()` and `subscriptions()` return,
    /// because a page hands all four to the one consumer that parses them. An
    /// object would buy destructuring at the price of the `json_compatible` care
    /// [`tick`](Self::tick) documents, for a payload read once per edit rather
    /// than once per pass. The rendered diff and the loops a version adds above
    /// the start of what they read stay off it: those two are the control port's
    /// reply to an author at a terminal, and a page re-reads `snapshot()` after
    /// an accepted reload, whose source and IR panes are the new version.
    ///
    /// Throws the rendered diagnostics for a version that does not compile, or
    /// that cannot take over the state the running program is holding. Such a
    /// throw leaves the running program answering, at the generation this last
    /// reported: the version is compiled and checked before anything is torn
    /// down. A typo is a caught exception and a stale page, not a program that
    /// stops.
    pub fn reload(&mut self, source: &str) -> Result<String, JsValue> {
        let report = self.host.reload(source).map_err(|e| match *e {
            // The rendered diagnostics rather than the error's `Display`, which
            // is the compiler errors' `Debug`. The page has the rejected source
            // in an editor, so a report naming a line and a column lands on
            // something its reader can see. `<new>` names that source here and
            // in the control port's `/reload`, neither having a file behind it.
            EmbedError::Compile(errors) => {
                JsValue::from_str(&render_errors(&errors, "<new>", source))
            }
            other => JsValue::from_str(&other.to_string()),
        })?;
        let ReuseTally { kept, bound } = report.reuse;
        Ok(serde_json::json!({
            "generation": self.host.generation(),
            "kept": kept,
            "bound": bound,
        })
        .to_string())
    }

    /// The `/api/snapshot` payload for the running version.
    ///
    /// What the inspector renders its source and IR panes from. Computed at
    /// compile and re-rendered by an accepted [`reload`](Self::reload), which is
    /// when a page re-reads it: the version it describes is the one
    /// `meta.generation` names.
    pub fn snapshot(&self) -> String {
        self.host.snapshot().to_string()
    }

    /// What the program subscribes to, as
    /// `[{source, endpoint, feed, products}]`.
    ///
    /// The page owns the WebSocket. A `wasm_socket_subscribe` in the program
    /// binds a declared source and says what fills it; this is how the page
    /// learns what to connect to, so the endpoint and the products live in the
    /// program rather than in two places that have to agree. What comes back
    /// off the socket is decoded by the page and pushed into `source` through
    /// [`push`](Self::push), like any other source — there is no socket in the
    /// module, and on `wasm32` there could not be one.
    ///
    /// Read after `compile` and after an accepted [`reload`](Self::reload),
    /// which replaces the list rather than adding to it: a feed that leaves it
    /// is a socket the page should close, and one that arrives or changes its
    /// products is one it should open.
    pub fn subscriptions(&self) -> Result<String, JsValue> {
        serde_json::to_string(self.host.socket_subscriptions())
            .map_err(|e| JsValue::from_str(&format!("subscriptions: {e}")))
    }

    /// Append `rows` to the source named `source`.
    ///
    /// `rows` is a JSON array of objects matching the source's declared row
    /// type. A missing, extra or mistyped field throws.
    pub fn push(&mut self, source: &str, rows: JsValue) -> Result<(), JsValue> {
        let row_type = self
            .host
            .channels()
            .source(source)
            .ok_or_else(|| JsValue::from_str(&format!("no source named '{source}'")))?
            .borrow()
            .row_type()
            .clone();
        let decoded = decode_rows(rows, &row_type, source)?;
        self.host
            .push(source, decoded)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Make one call against the route `method path`, as `rows`.
    ///
    /// The page is the listener a `wasm_serve` in the program binds, so this is
    /// what a `fetch` in the page turns into: the request crosses as rows of the
    /// route's declared record type rather than as a body, and the reply comes
    /// back in the next `tick`'s `outputs` under the route's own name
    /// (`"PATCH /cart"`). Nothing in the program parses or renders a body.
    pub fn request(&mut self, method: &str, path: &str, rows: JsValue) -> Result<(), JsValue> {
        let (source, _) = self
            .host
            .channels()
            .route(method, path)
            .ok_or_else(|| JsValue::from_str(&format!("no route serves '{method} {path}'")))?;
        let row_type = source.borrow().row_type().clone();
        let decoded = decode_rows(rows, &row_type, &format!("{method} {path}"))?;
        self.host
            .request(method, path, decoded)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Say that no further rows will arrive on `source`.
    pub fn close(&mut self, source: &str) -> Result<(), JsValue> {
        self.host
            .close(source)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }

    /// Advance the program once, and return what its sinks produced as
    /// `{outputs: [{sink, rows}], produced, done}`.
    pub fn tick(&mut self) -> Result<JsValue, JsValue> {
        let result = self.host.tick();
        let mut outputs = Vec::with_capacity(result.outputs.len());
        for (sink, rows) in &result.outputs {
            let mut encoded = Vec::with_capacity(rows.len());
            for row in rows {
                encoded.push(
                    row_to_json(row)
                        .map_err(|e| JsValue::from_str(&format!("row from '{sink}': {e}")))?,
                );
            }
            outputs.push(serde_json::json!({ "sink": sink, "rows": encoded }));
        }
        let payload = serde_json::json!({
            "outputs": outputs,
            "produced": result.produced,
            "done": result.done,
        });
        // `json_compatible`, because the default serializer renders a map as a
        // JS `Map` rather than an object, and a caller reaching for
        // `result.outputs` on a `Map` reads `undefined`.
        payload
            .serialize(&serde_wasm_bindgen::Serializer::json_compatible())
            .map_err(|e| JsValue::from_str(&format!("tick result: {e}")))
    }

    /// The live frame for what the program has produced.
    ///
    /// The same bytes the native inspector's websocket sends, so the frontend
    /// consumes one format whichever host it is attached to. Worth rendering on
    /// a tick that reported `produced`; on any other it repeats what the last
    /// one said.
    pub fn frame(&self, final_frame: bool) -> String {
        self.host.frame(final_frame)
    }
}
