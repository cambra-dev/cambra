//! `POST /api/reload` and `POST /api/restart`: the inspector's source pane
//! reloading `main` with the text the reader edited, or restarting the program
//! from it.
//!
//! Each route hands the text to the main loop as the control port's own
//! request, [`ControlRequest::Reload`] or [`ControlRequest::Restart`], through
//! a [`ControlClient`] onto the same queue, and
//! [`service`](crate::control_port::service) answers it. So a reload or a
//! restart from the page and one from the control port are one operation, and
//! the page sees the new version the way it sees any new version of `main`:
//! through `src/inspector_model/design.md`, "A reload of main is followed".
//!
//! The routes exist only on a run started with `--control`. Without one there
//! is no queue to send to, each route answers `404`, and `GET
//! /api/capabilities` says `false` for both, which leaves the page's source
//! pane read-only.
//!
//! # Admission
//!
//! A reload or a restart runs the code it carries, and the server is reachable from every
//! page the reader's browser loads. [`admit`] refuses each way such a page can
//! reach it:
//!
//! - **A cross-site form or `no-cors` fetch.** Its body can only be a
//!   CORS-safelisted type, which `application/json` is not, so the route takes
//!   `application/json` and nothing else. A cross-site `fetch` that sets the
//!   type is preflighted, and the server answers no preflight.
//! - **A cross-site request that did get through.** A browser sends `Origin` on
//!   every `POST`, so an `Origin` naming another host is refused. An absent
//!   `Origin` is a client that is not a browser: `curl`, a script, an editor.
//! - **DNS rebinding.** A page served from a name the attacker re-points at
//!   `127.0.0.1` is same-origin with the server, and its `Origin` matches its
//!   `Host`. So `Host` must name loopback itself.

use serde::Deserialize;

use crate::control_port::{
    ControlClient, ControlReply, ControlRequest, header_value, is_loopback_host,
};
use crate::live_program::MAIN_BRANCH;

/// What a posted version asks of the program.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Verb {
    /// Reload `main`, carrying its state forward.
    Reload,
    /// Discard every branch and run the version from a fresh compile.
    Restart,
}

impl Verb {
    /// The verb whose route `path` is, if it is one.
    pub fn at(path: &str) -> Option<Verb> {
        match path {
            "/api/reload" => Some(Verb::Reload),
            "/api/restart" => Some(Verb::Restart),
            _ => None,
        }
    }

    /// The control-port request carrying `source`.
    fn request(self, source: String) -> ControlRequest {
        match self {
            Verb::Reload => ControlRequest::Reload {
                branch: MAIN_BRANCH.to_string(),
                code: source,
            },
            Verb::Restart => ControlRequest::Restart { code: source },
        }
    }
}

/// The body `POST /api/reload` and `POST /api/restart` take.
#[derive(Deserialize)]
struct ReloadBody {
    /// The version's source: the root file's whole text.
    source: String,
}

/// Why [`admit`] refused a request: the status and the message to send.
#[derive(Debug, PartialEq)]
pub struct Refusal {
    pub status: u16,
    pub message: String,
}

impl Refusal {
    fn new(status: u16, message: impl Into<String>) -> Self {
        Self {
            status,
            message: message.into(),
        }
    }
}

/// Whether a request with these headers may reload or restart the program; see
/// the module docs, "Admission".
pub fn admit(
    method: &str,
    host: Option<&str>,
    origin: Option<&str>,
    content_type: Option<&str>,
) -> Result<(), Refusal> {
    if !method.eq_ignore_ascii_case("POST") {
        return Err(Refusal::new(
            405,
            format!("{method} cannot change the program; send POST"),
        ));
    }
    let Some(host) = host.filter(|host| is_loopback_host(host)) else {
        return Err(Refusal::new(
            403,
            format!(
                "the Host header {} does not name loopback",
                host.map_or("(absent)".to_string(), |h| format!("`{h}`"))
            ),
        ));
    };
    if let Some(origin) = origin
        && origin != format!("http://{host}")
    {
        return Err(Refusal::new(
            403,
            format!("a page at `{origin}` cannot change a program served at `{host}`"),
        ));
    }
    let media_type = content_type.map(|ct| ct.split(';').next().unwrap_or("").trim());
    if !media_type.is_some_and(|mt| mt.eq_ignore_ascii_case("application/json")) {
        return Err(Refusal::new(
            415,
            "send the version as `application/json`: {\"source\": \"…\"}",
        ));
    }
    Ok(())
}

/// The `GET /api/capabilities` body: what this run lets the page do. A run with
/// a control port takes both verbs, and one without takes neither.
pub fn capabilities_body(control: bool) -> String {
    serde_json::json!({ "reload": control, "restart": control }).to_string()
}

/// The JSON body for a [`ControlReply`]: its text as `message`, the posted
/// version's diagnostics, and the reuse tally of an accepted reload.
fn reply_body(reply: &ControlReply) -> String {
    let mut body = serde_json::json!({
        "message": reply.body,
        "diagnostics": reply.diagnostics,
    });
    if let Some(reuse) = reply.reuse {
        body["kept"] = reuse.kept.into();
        body["bound"] = reuse.bound.into();
    }
    body.to_string()
}

/// A reply carrying only a message.
fn message_body(message: &str) -> String {
    serde_json::json!({ "message": message, "diagnostics": [] }).to_string()
}

/// Answer one `POST` to `verb`'s route, blocking until the main loop has.
///
/// Called on a thread of its own, so the compile the main loop runs does not
/// hold up the snapshot and live routes the page uses meanwhile.
pub fn answer(mut request: tiny_http::Request, control: Option<ControlClient>, verb: Verb) {
    let admitted = admit(
        request.method().as_str(),
        header_value(&request, "Host").as_deref(),
        header_value(&request, "Origin").as_deref(),
        header_value(&request, "Content-Type").as_deref(),
    );
    let (status, body) = match admitted {
        Err(refusal) => (refusal.status, message_body(&refusal.message)),
        Ok(()) => match control {
            None => (
                404,
                message_body(
                    "this run has no control port; start it with `--control` to reload or restart",
                ),
            ),
            Some(control) => {
                let mut text = String::new();
                let parsed = request
                    .as_reader()
                    .read_to_string(&mut text)
                    .map_err(|e| e.to_string())
                    .and_then(|_| {
                        serde_json::from_str::<ReloadBody>(&text).map_err(|e| e.to_string())
                    });
                match parsed {
                    Err(e) => (400, message_body(&format!("not a version body: {e}"))),
                    Ok(ReloadBody { source }) => {
                        let reply = control.ask(verb.request(source));
                        (reply.status, reply_body(&reply))
                    }
                }
            }
        },
    };
    let content_type: tiny_http::Header = "Content-Type: application/json"
        .parse()
        .expect("static header parses");
    let response = tiny_http::Response::from_string(body)
        .with_status_code(status)
        .with_header(content_type);
    if let Err(e) = request.respond(response) {
        eprintln!("cambra: responding to a {verb:?} failed: {e}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const JSON: Option<&str> = Some("application/json");

    #[test]
    fn a_same_origin_json_post_is_admitted() {
        let host = Some("localhost:8080");
        let origin = Some("http://localhost:8080");
        assert_eq!(admit("POST", host, origin, JSON), Ok(()));
        assert_eq!(
            admit(
                "POST",
                host,
                origin,
                Some("application/json; charset=utf-8")
            ),
            Ok(())
        );
    }

    /// A client that is not a browser sends no `Origin`, and is admitted.
    #[test]
    fn a_post_with_no_origin_is_admitted() {
        assert_eq!(admit("POST", Some("127.0.0.1:8080"), None, JSON), Ok(()));
    }

    #[test]
    fn a_page_on_another_origin_is_refused() {
        let refusal = admit(
            "POST",
            Some("localhost:8080"),
            Some("http://example.com"),
            JSON,
        )
        .unwrap_err();
        assert_eq!(refusal.status, 403);
    }

    /// The DNS-rebinding shape: `Origin` matches `Host`, and `Host` is a name the
    /// attacker re-pointed at loopback.
    #[test]
    fn a_host_that_does_not_name_loopback_is_refused() {
        let refusal = admit(
            "POST",
            Some("rebind.example:8080"),
            Some("http://rebind.example:8080"),
            JSON,
        )
        .unwrap_err();
        assert_eq!(refusal.status, 403);
        assert_eq!(admit("POST", None, None, JSON).unwrap_err().status, 403);
    }

    /// A cross-site form or `no-cors` fetch can only send a CORS-safelisted
    /// type, so taking JSON alone keeps it out.
    #[test]
    fn a_body_that_is_not_json_is_refused() {
        let host = Some("localhost:8080");
        for content_type in [
            None,
            Some("text/plain"),
            Some("application/x-www-form-urlencoded"),
        ] {
            assert_eq!(
                admit("POST", host, None, content_type).unwrap_err().status,
                415,
                "{content_type:?}"
            );
        }
    }

    #[test]
    fn each_verb_has_its_route() {
        assert_eq!(Verb::at("/api/reload"), Some(Verb::Reload));
        assert_eq!(Verb::at("/api/restart"), Some(Verb::Restart));
        assert_eq!(Verb::at("/api/snapshot"), None);
    }

    #[test]
    fn a_method_other_than_post_is_refused() {
        let refusal = admit("GET", Some("localhost:8080"), None, JSON).unwrap_err();
        assert_eq!(refusal.status, 405);
    }
}
