//! Control port: HTTP endpoints for diffing a running program against a new
//! version of its source, and for replacing it with that version.
//!
//! Two endpoints, both taking the new source as their argument:
//!
//! - `/diff` — how the new version differs from the running one, rendered as an
//!   annotated tree. Answers the question without changing anything.
//! - `/update` — replace the running program with the new version.
//!
//! The source may be the whole query string, percent-decoded, or a `POST` body.
//! A `stage=` parameter selects where in the pipeline `/diff` compares (see
//! [`stage_from_name`]); it must come first when the query also carries the
//! source.
//!
//! # Why requests are handed to the main loop
//!
//! Nothing on the interpreter side is [`Send`]: the operator graph, the sources,
//! and the compilation contexts are `Rc`/`RefCell` throughout, and compiling a
//! new version needs all three. So the server thread does no compilation. It
//! parses the request into a [`ControlRequest`], sends it to the main loop over
//! a channel, and blocks on the reply — the main loop services it between ticks,
//! where it already holds the program exclusively.

use std::sync::mpsc::{Receiver, SyncSender, sync_channel};
use std::thread;

use log::info;

use crate::ccl::context::CompileStage;

/// What a control-port client asked for.
pub enum ControlRequest {
    /// Report how `code` differs from the running program, comparing at `stage`.
    Diff { code: String, stage: CompileStage },
    /// Replace the running program with `code`.
    Update { code: String },
}

/// The answer to one [`ControlRequest`], as an HTTP status and a plain-text body.
#[derive(Debug)]
pub struct ControlReply {
    pub status: u16,
    pub body: String,
}

impl ControlReply {
    /// A `200` carrying `body`.
    pub fn ok(body: impl Into<String>) -> Self {
        Self {
            status: 200,
            body: body.into(),
        }
    }

    /// A `400` carrying `body` — the request named a version the running
    /// program cannot compile or cannot adopt.
    pub fn rejected(body: impl Into<String>) -> Self {
        Self {
            status: 400,
            body: body.into(),
        }
    }
}

/// One request awaiting an answer, together with the channel the server thread
/// is blocked on.
///
/// Consumed by [`answer`](Self::answer), so a serviced request cannot be left
/// unanswered by accident; dropping one instead unblocks the server thread with
/// a `503`.
pub struct ControlMessage {
    request: ControlRequest,
    reply: Option<SyncSender<ControlReply>>,
}

impl ControlMessage {
    /// What was asked.
    pub fn request(&self) -> &ControlRequest {
        &self.request
    }

    /// Answer the request and release the server thread.
    pub fn answer(mut self, reply: ControlReply) {
        if let Some(tx) = self.reply.take() {
            let _ = tx.send(reply);
        }
    }
}

impl Drop for ControlMessage {
    fn drop(&mut self) {
        if let Some(tx) = self.reply.take() {
            let _ = tx.send(ControlReply {
                status: 503,
                body: "control request dropped without an answer\n".to_string(),
            });
        }
    }
}

/// The main loop's end of the control port.
///
/// Holding one keeps the server thread's channel open; dropping it makes every
/// later request fail rather than hang.
pub struct ControlPort {
    rx: Receiver<ControlMessage>,
}

impl ControlPort {
    /// Start the control server on `port`.
    pub fn new(port: u16) -> Self {
        let (tx, rx) = sync_channel::<ControlMessage>(0);

        thread::spawn(move || {
            let server = tiny_http::Server::http(format!("0.0.0.0:{port}"))
                .expect("Failed to start control port server");
            info!("Control port running at http://localhost:{port}");

            for mut request in server.incoming_requests() {
                let mut body = String::new();
                let _ = std::io::Read::read_to_string(request.as_reader(), &mut body);
                let reply = match parse_request(request.url(), &body) {
                    Err(reply) => reply,
                    Ok(parsed) => {
                        let (reply_tx, reply_rx) = sync_channel::<ControlReply>(0);
                        let message = ControlMessage {
                            request: parsed,
                            reply: Some(reply_tx),
                        };
                        // A closed channel means the program is gone; a closed
                        // reply channel means the main loop dropped the message
                        // without the `Drop` answer arriving, which is a bug
                        // rather than a state to report differently.
                        match tx.send(message) {
                            Err(_) => ControlReply {
                                status: 503,
                                body: "program is not accepting control requests\n".to_string(),
                            },
                            Ok(()) => reply_rx.recv().unwrap_or(ControlReply {
                                status: 500,
                                body: "control request was never answered\n".to_string(),
                            }),
                        }
                    }
                };
                let header: tiny_http::Header =
                    "Content-Type: text/plain; charset=utf-8".parse().unwrap();
                let _ = request.respond(
                    tiny_http::Response::from_string(reply.body)
                        .with_status_code(reply.status)
                        .with_header(header),
                );
            }
        });

        ControlPort { rx }
    }

    /// Take the next pending request, or `None` if none is waiting.
    ///
    /// Non-blocking: the main loop calls this at a tick boundary and carries on
    /// when nothing is queued.
    pub fn poll(&self) -> Option<ControlMessage> {
        self.rx.try_recv().ok()
    }
}

/// The pipeline stage a `stage=` parameter names.
///
/// The default, and the point [`ControlRequest::Diff`] uses when the parameter
/// is absent, is `channelized` — the last stage before lambda elimination, so
/// the tree still has the binders and the shape the source was written in while
/// the mutability and channelization rewrites have already been normalized
/// away. See [`CompileStage`] for what each stage normalizes.
pub fn stage_from_name(name: &str) -> Option<CompileStage> {
    Some(match name {
        "lowered" => CompileStage::Lowered,
        "inferred" => CompileStage::Inferred,
        "inlined" => CompileStage::Inlined,
        "channelized" => CompileStage::Channelized,
        "lambda-elim" => CompileStage::LambdaElim,
        "planned" => CompileStage::Planned,
        _ => return None,
    })
}

/// Every `stage=` spelling, for a diagnostic.
const STAGE_NAMES: &str = "lowered, inferred, inlined, channelized, lambda-elim, planned";

/// Split a URL into its path and its raw query string.
fn split_url(url: &str) -> (&str, &str) {
    match url.split_once('?') {
        Some((path, query)) => (path, query),
        None => (url, ""),
    }
}

/// Parse a request into the [`ControlRequest`] the main loop services, or the
/// reply to send when it is not one.
fn parse_request(url: &str, body: &str) -> Result<ControlRequest, ControlReply> {
    let (path, query) = split_url(url);
    let (stage_name, rest) = split_stage_param(query);

    // The source is the body when there is one, so a program containing `&` or
    // `#` need not be percent-encoded to survive the query string.
    let code = if body.trim().is_empty() {
        percent_decode(rest)
    } else {
        body.to_string()
    };

    match path {
        "/diff" => {
            let stage = match stage_name {
                None => CompileStage::Channelized,
                Some(name) => stage_from_name(name).ok_or_else(|| {
                    ControlReply::rejected(format!(
                        "unknown stage {name:?}; expected one of: {STAGE_NAMES}\n"
                    ))
                })?,
            };
            require_code(&code)?;
            Ok(ControlRequest::Diff { code, stage })
        }
        "/update" => {
            require_code(&code)?;
            Ok(ControlRequest::Update { code })
        }
        _ => Err(ControlReply {
            status: 404,
            body: "endpoints: /diff?<source>, /update?<source>\n".to_string(),
        }),
    }
}

fn require_code(code: &str) -> Result<(), ControlReply> {
    if code.trim().is_empty() {
        return Err(ControlReply::rejected(
            "no source given: pass it as the query string or the request body\n",
        ));
    }
    Ok(())
}

/// Peel a leading `stage=<name>&` off a query string.
///
/// Leading rather than anywhere, because everything after it is the source
/// program and an `&` inside a program must not be read as a parameter
/// separator.
fn split_stage_param(query: &str) -> (Option<&str>, &str) {
    let Some(rest) = query.strip_prefix("stage=") else {
        return (None, query);
    };
    match rest.split_once('&') {
        Some((name, code)) => (Some(name), code),
        None => (Some(rest), ""),
    }
}

/// Decode `application/x-www-form-urlencoded` text: `%XX` escapes and `+` for
/// space.
///
/// An incomplete or non-hex `%` escape is left as written rather than rejected —
/// a bare `%` is a modulus in CHL, so a client that percent-encoded nothing
/// still gets its program through.
fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' if i + 2 < bytes.len() => {
                let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).ok();
                match hex.and_then(|h| u8::from_str_radix(h, 16).ok()) {
                    Some(byte) => {
                        out.push(byte);
                        i += 3;
                    }
                    None => {
                        out.push(bytes[i]);
                        i += 1;
                    }
                }
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn diff_of(url: &str) -> (String, CompileStage) {
        match parse_request(url, "").expect("parses") {
            ControlRequest::Diff { code, stage } => (code, stage),
            ControlRequest::Update { .. } => panic!("expected a diff request"),
        }
    }

    #[test]
    fn diff_defaults_to_the_stage_before_lambda_elimination() {
        let (code, stage) = diff_of("/diff?x%20%3D%201%3B%20x");
        assert_eq!(code, "x = 1; x");
        assert_eq!(stage, CompileStage::Channelized);
    }

    #[test]
    fn a_leading_stage_parameter_selects_the_diff_point() {
        let (code, stage) = diff_of("/diff?stage=inferred&x = 1; x");
        assert_eq!(code, "x = 1; x");
        assert_eq!(stage, CompileStage::Inferred);
    }

    /// A `&` after the source's first character is part of the program, not a
    /// parameter separator — only a *leading* `stage=` is peeled.
    #[test]
    fn an_ampersand_in_the_source_is_not_a_parameter_separator() {
        let (code, _) = diff_of("/diff?a = 1 & 2; a");
        assert_eq!(code, "a = 1 & 2; a");
    }

    #[test]
    fn a_bare_percent_survives_decoding() {
        let (code, _) = diff_of("/diff?x = 7 % 3; x");
        assert_eq!(code, "x = 7 % 3; x");
    }

    #[test]
    fn a_body_supplies_the_source_when_the_query_does_not() {
        let request = parse_request("/update", "y = 2; y").expect("parses");
        match request {
            ControlRequest::Update { code } => assert_eq!(code, "y = 2; y"),
            ControlRequest::Diff { .. } => panic!("expected an update request"),
        }
    }

    #[test]
    fn an_unknown_stage_is_rejected_rather_than_defaulted() {
        let reply = parse_request("/diff?stage=nonsense&x", "")
            .err()
            .expect("rejected");
        assert_eq!(reply.status, 400);
        assert!(reply.body.contains("channelized"), "{}", reply.body);
    }

    #[test]
    fn a_request_with_no_source_is_rejected() {
        let reply = parse_request("/diff", "").err().expect("rejected");
        assert_eq!(reply.status, 400);
    }

    #[test]
    fn an_unserviced_message_unblocks_its_caller() {
        let (tx, rx) = sync_channel::<ControlReply>(0);
        let waiter = thread::spawn(move || rx.recv().expect("a reply").status);
        drop(ControlMessage {
            request: ControlRequest::Update {
                code: "x".to_string(),
            },
            reply: Some(tx),
        });
        assert_eq!(waiter.join().unwrap(), 503);
    }
}
