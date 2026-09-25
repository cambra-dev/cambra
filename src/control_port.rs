//! Control port: HTTP endpoints for diffing a running program against a new
//! version of its source, for replacing a branch's version with it, and for
//! creating, deleting, retargeting and listing branches.
//!
//! Dispatch is on the path alone. A `<branch>` segment that is omitted means
//! `production` ([`ROOT`]), and a name is one path segment of ASCII letters,
//! digits, `-` and `_` ([`is_branch_name`]):
//!
//! - `/diff[/<branch>]` — how the new version differs from the one a reload of
//!   the branch would diff against, rendered as an annotated tree. Answers the
//!   question without changing anything.
//! - `/reload[/<branch>]` — replace the branch's version with the new one.
//! - `/branch/<name>[/from/<origin>]` — create a branch as a copy of `origin`.
//! - `/branch/<name>/delete` — delete a branch.
//! - `/branch/<name>/retarget/<origin>` — make `origin` the branch's origin.
//! - `/branches/list` — one line per branch.
//!
//! The verb table and its status codes are `src/ccl/design/program-evolution.md`,
//! "The control port".
//!
//! The source may be the whole query string, percent-decoded, or a `POST` body.
//! The query form is percent-encoded rather than form-encoded: `+` stands for
//! itself, because it is addition and string concatenation in CHL (see
//! [`percent_decode`]).
//! A `phase=` parameter selects where in the pipeline `/diff` compares (see
//! [`OFFERED_PHASES`]); it must come first when the query also carries the
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

use crate::ccl::context::Phase;
use crate::live_program::{ROOT, is_branch_name};

/// What a control-port client asked for.
#[derive(Debug, PartialEq)]
pub enum ControlRequest {
    /// Report how `code` differs from the version a reload of `branch` would
    /// diff against, comparing at `phase`.
    Diff {
        branch: String,
        code: String,
        phase: Phase,
    },
    /// Replace `branch`'s version with `code`.
    Reload { branch: String, code: String },
    /// Create branch `name` as a copy of `origin`'s entry.
    CreateBranch { name: String, origin: String },
    /// Delete branch `name`.
    DeleteBranch { name: String },
    /// Make `origin` the origin of branch `name`.
    RetargetBranch { name: String, origin: String },
    /// List every branch.
    ListBranches,
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
    /// program cannot compile or cannot take over the running state, or asked
    /// for a branch operation that is refused.
    pub fn rejected(body: impl Into<String>) -> Self {
        Self {
            status: 400,
            body: body.into(),
        }
    }

    /// A `404` carrying `body` — an unknown path, or a branch name the table
    /// does not hold.
    pub fn not_found(body: impl Into<String>) -> Self {
        Self {
            status: 404,
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
    ///
    /// Binds before spawning the dispatcher, so a port already in use is an
    /// error the caller reports rather than a panic on a detached thread that
    /// leaves the program running with no control port and nothing saying so.
    pub fn new(port: u16) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let (tx, rx) = sync_channel::<ControlMessage>(0);
        let server = tiny_http::Server::http(format!("0.0.0.0:{port}"))?;
        info!("Control port running at http://localhost:{port}");

        thread::spawn(move || {
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

        Ok(ControlPort { rx })
    }

    /// Take the next pending request, or `None` if none is waiting.
    ///
    /// Non-blocking: the main loop calls this at a tick boundary and carries on
    /// when nothing is queued.
    pub fn poll(&self) -> Option<ControlMessage> {
        self.rx.try_recv().ok()
    }
}

/// Every pipeline position `/diff` offers, with the `phase=` spelling that names
/// it.
///
/// The compiler can stop at any [`Phase`]'s output; this table is the subset the
/// control port offers, and it leaves out the three that answer no question a
/// caller of `/diff` has — `uniquify`, whose tree diffs identically to `lowered`
/// because the hash is uid-robust, and `transact`/`letrec`, which are the two
/// halves of one rewrite and report a shape mid-rewrite.
///
/// One table rather than a lookup beside a list of spellings, so the set a
/// caller may name, the set the rejection diagnostic offers, and the set
/// `every_offered_phase_is_a_diff_point` exercises are the same set.
pub const OFFERED_PHASES: &[(&str, Phase)] = &[
    ("lowered", Phase::Lower),
    ("inferred", Phase::Infer),
    ("inlined", Phase::Inline),
    ("channelized", Phase::Channelize),
    ("as-of-read", Phase::AsOfRead),
    ("lambda-elim", Phase::LambdaElim),
    ("planned", Phase::Planning),
];

/// The phase `/diff` compares at when the request names none: `as-of-read`, the
/// last position at which the tree still has binders, and the one `lambda_elim`
/// consumes. The mutability and channelization rewrites are complete there and
/// an edit still localizes the way it does further up — see
/// `src/ccl/design/diffing.md`, "Which phase to diff".
pub const DEFAULT_PHASE: Phase = Phase::AsOfRead;

/// The phase a `phase=` spelling names, or `None` when it names none.
pub fn phase_from_name(name: &str) -> Option<Phase> {
    OFFERED_PHASES
        .iter()
        .find(|(spelling, _)| *spelling == name)
        .map(|(_, phase)| *phase)
}

/// Every `phase=` spelling, for a diagnostic.
fn phase_names() -> String {
    OFFERED_PHASES
        .iter()
        .map(|(spelling, _)| *spelling)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Split a URL into its path and its raw query string.
fn split_url(url: &str) -> (&str, &str) {
    match url.split_once('?') {
        Some((path, query)) => (path, query),
        None => (url, ""),
    }
}

/// The reply to a path that names no verb.
fn unknown_path() -> ControlReply {
    ControlReply::not_found(
        "endpoints: /diff[/<branch>]?<source>, /reload[/<branch>]?<source>, \
/branch/<name>[/from/<origin>], /branch/<name>/delete, /branch/<name>/retarget/<origin>, \
/branches/list\n",
    )
}

/// The verb a path names, with the branch names it carries, or `None` for a
/// path that names none.
///
/// A segment that is not a branch name is a path that names no verb, so it
/// answers 404 like any other unknown path rather than reaching the table.
fn parse_path(path: &str) -> Option<Verb<'_>> {
    let segments: Vec<&str> = path.strip_prefix('/')?.split('/').collect();
    let verb = match segments.as_slice() {
        ["diff"] => Verb::Diff(ROOT),
        ["diff", branch] => Verb::Diff(branch),
        ["reload"] => Verb::Reload(ROOT),
        ["reload", branch] => Verb::Reload(branch),
        ["branch", n] => Verb::Create(n, ROOT),
        ["branch", n, "from", origin] => Verb::Create(n, origin),
        ["branch", n, "delete"] => Verb::Delete(n),
        ["branch", n, "retarget", origin] => Verb::Retarget(n, origin),
        ["branches", "list"] => Verb::List,
        _ => return None,
    };
    verb.names().into_iter().all(is_branch_name).then_some(verb)
}

/// A verb and the branch names its path carries, before the source is read.
enum Verb<'a> {
    Diff(&'a str),
    Reload(&'a str),
    Create(&'a str, &'a str),
    Delete(&'a str),
    Retarget(&'a str, &'a str),
    List,
}

impl Verb<'_> {
    fn names(&self) -> Vec<&str> {
        match *self {
            Verb::Diff(b) | Verb::Reload(b) | Verb::Delete(b) => vec![b],
            Verb::Create(n, o) | Verb::Retarget(n, o) => vec![n, o],
            Verb::List => vec![],
        }
    }
}

/// Parse a request into the [`ControlRequest`] the main loop services, or the
/// reply to send when it is not one.
fn parse_request(url: &str, body: &str) -> Result<ControlRequest, ControlReply> {
    let (path, query) = split_url(url);
    let verb = parse_path(path).ok_or_else(unknown_path)?;
    // Only `/diff` takes a phase, so only `/diff` peels one. On `/reload` a
    // leading `phase=` is the program's own first characters.
    let (phase_name, rest) = if matches!(verb, Verb::Diff(_)) {
        split_phase_param(query)
    } else {
        (None, query)
    };

    // The source is the body when there is one, so a program containing `&` or
    // `#` need not be percent-encoded to survive the query string.
    let code = || {
        if body.trim().is_empty() {
            percent_decode(rest)
        } else {
            body.to_string()
        }
    };

    match verb {
        Verb::Diff(branch) => {
            let phase = match phase_name {
                None => DEFAULT_PHASE,
                Some(name) => phase_from_name(name).ok_or_else(|| {
                    ControlReply::rejected(format!(
                        "unknown phase {name:?}; expected one of: {}\n",
                        phase_names()
                    ))
                })?,
            };
            let code = code();
            require_code(&code)?;
            Ok(ControlRequest::Diff {
                branch: branch.to_string(),
                code,
                phase,
            })
        }
        Verb::Reload(branch) => {
            let code = code();
            require_code(&code)?;
            Ok(ControlRequest::Reload {
                branch: branch.to_string(),
                code,
            })
        }
        Verb::Create(name, origin) => Ok(ControlRequest::CreateBranch {
            name: name.to_string(),
            origin: origin.to_string(),
        }),
        Verb::Delete(name) => Ok(ControlRequest::DeleteBranch {
            name: name.to_string(),
        }),
        Verb::Retarget(name, origin) => Ok(ControlRequest::RetargetBranch {
            name: name.to_string(),
            origin: origin.to_string(),
        }),
        Verb::List => Ok(ControlRequest::ListBranches),
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

/// Peel a leading `phase=<name>&` off a query string.
///
/// Leading rather than anywhere, because everything after it is the source
/// program and an `&` inside a program must not be read as a parameter
/// separator.
///
/// `<name>` has to look like one of the spellings in [`OFFERED_PHASES`] — all
/// lowercase letters and hyphens — or nothing is peeled. `phase=1; phase` is a
/// valid CHL program, and reading its first token as a phase name would reject
/// the program instead of compiling it. A name of the right shape that names no
/// phase is still peeled, so a misspelling gets the diagnostic listing the
/// spellings rather than a compile error against a program nobody wrote.
fn split_phase_param(query: &str) -> (Option<&str>, &str) {
    let Some(rest) = query.strip_prefix("phase=") else {
        return (None, query);
    };
    let (name, code) = match rest.split_once('&') {
        Some((name, code)) => (name, code),
        None => (rest, ""),
    };
    let names_a_phase =
        !name.is_empty() && name.chars().all(|c| c.is_ascii_lowercase() || c == '-');
    if names_a_phase {
        (Some(name), code)
    } else {
        (None, query)
    }
}

/// Decode the `%XX` escapes in a query string.
///
/// An incomplete or non-hex `%` escape is left as written rather than rejected —
/// a bare `%` is a modulus in CHL, so a client that percent-encoded nothing
/// still gets its program through.
///
/// `+` is left alone for the same reason, which is where this stops being
/// `application/x-www-form-urlencoded`: `+` is addition and string concatenation
/// in CHL and a space is neither, so decoding it to one silently rewrote
/// `x = 1 + 2` to `x = 1   2`, and `"a+b"` to `"a b"`. A client that wants a
/// space writes one, or writes `%20`.
fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
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

    fn diff_of(url: &str) -> (String, Phase) {
        match parse_request(url, "").expect("parses") {
            ControlRequest::Diff { code, phase, .. } => (code, phase),
            other => panic!("expected a diff request, got {other:?}"),
        }
    }

    #[test]
    fn diff_defaults_to_the_phase_before_lambda_elimination() {
        let (code, phase) = diff_of("/diff?x%20%3D%201%3B%20x");
        assert_eq!(code, "x = 1; x");
        assert_eq!(phase, Phase::AsOfRead);
    }

    #[test]
    fn a_leading_phase_parameter_selects_the_diff_point() {
        let (code, phase) = diff_of("/diff?phase=inferred&x = 1; x");
        assert_eq!(code, "x = 1; x");
        assert_eq!(phase, Phase::Infer);
    }

    /// A `&` after the source's first character is part of the program, not a
    /// parameter separator — only a *leading* `phase=` is peeled.
    #[test]
    fn an_ampersand_in_the_source_is_not_a_parameter_separator() {
        let (code, _) = diff_of("/diff?a = 1 & 2; a");
        assert_eq!(code, "a = 1 & 2; a");
    }

    /// `+` is addition and string concatenation in CHL, so the query form leaves
    /// it alone rather than reading it as a form-encoded space.
    #[test]
    fn a_plus_in_the_source_is_not_a_space() {
        let (code, _) = diff_of("/diff?x = 1 + 2; x");
        assert_eq!(code, "x = 1 + 2; x");
    }

    /// A program whose first token happens to be `phase=…` is a program, not a
    /// parameter: only a name shaped like one of the offered spellings is peeled.
    #[test]
    fn a_program_starting_with_phase_is_not_a_parameter() {
        let (code, phase) = diff_of("/diff?phase=1; phase");
        assert_eq!(code, "phase=1; phase");
        assert_eq!(phase, DEFAULT_PHASE);
    }

    /// `/reload` takes no phase, so a leading `phase=` there is source.
    #[test]
    fn reload_does_not_peel_a_phase() {
        let request = parse_request("/reload?phase=1; phase", "").expect("parses");
        match request {
            ControlRequest::Reload { code, .. } => assert_eq!(code, "phase=1; phase"),
            other => panic!("expected a reload request, got {other:?}"),
        }
    }

    #[test]
    fn a_bare_percent_survives_decoding() {
        let (code, _) = diff_of("/diff?x = 7 % 3; x");
        assert_eq!(code, "x = 7 % 3; x");
    }

    #[test]
    fn a_body_supplies_the_source_when_the_query_does_not() {
        let request = parse_request("/reload", "y = 2; y").expect("parses");
        match request {
            ControlRequest::Reload { code, .. } => assert_eq!(code, "y = 2; y"),
            other => panic!("expected a reload request, got {other:?}"),
        }
    }

    #[test]
    fn an_unknown_phase_is_rejected_rather_than_defaulted() {
        let reply = parse_request("/diff?phase=nonsense&x", "").expect_err("rejected");
        assert_eq!(reply.status, 400);
        assert!(reply.body.contains("channelized"), "{}", reply.body);
    }

    #[test]
    fn a_request_with_no_source_is_rejected() {
        let reply = parse_request("/diff", "").expect_err("rejected");
        assert_eq!(reply.status, 400);
    }

    fn parsed(url: &str) -> ControlRequest {
        parse_request(url, "").unwrap_or_else(|r| panic!("{url} refused: {r:?}"))
    }

    fn status_of(url: &str, body: &str) -> u16 {
        parse_request(url, body).expect_err("refused").status
    }

    /// An omitted `<branch>` segment means the root.
    #[test]
    fn diff_and_reload_address_production_without_a_branch_segment() {
        assert!(matches!(
            parse_request("/diff", "x").unwrap(),
            ControlRequest::Diff { branch, .. } if branch == ROOT
        ));
        assert!(matches!(
            parse_request("/reload", "x").unwrap(),
            ControlRequest::Reload { branch, .. } if branch == ROOT
        ));
    }

    #[test]
    fn diff_and_reload_take_a_branch_segment() {
        assert_eq!(
            parse_request("/diff/staging?phase=inferred&x = 1; x", "").unwrap(),
            ControlRequest::Diff {
                branch: "staging".to_string(),
                code: "x = 1; x".to_string(),
                phase: Phase::Infer,
            }
        );
        assert_eq!(
            parse_request("/reload/qa-2_b", "y").unwrap(),
            ControlRequest::Reload {
                branch: "qa-2_b".to_string(),
                code: "y".to_string(),
            }
        );
        assert_eq!(status_of("/reload/staging", ""), 400, "no source");
    }

    #[test]
    fn the_branch_verbs_parse_from_the_path_alone() {
        assert_eq!(
            parsed("/branch/staging"),
            ControlRequest::CreateBranch {
                name: "staging".to_string(),
                origin: ROOT.to_string(),
            }
        );
        assert_eq!(
            parsed("/branch/scratch/from/qa"),
            ControlRequest::CreateBranch {
                name: "scratch".to_string(),
                origin: "qa".to_string(),
            }
        );
        assert_eq!(
            parsed("/branch/scratch/delete"),
            ControlRequest::DeleteBranch {
                name: "scratch".to_string(),
            }
        );
        assert_eq!(
            parsed("/branch/scratch/retarget/production"),
            ControlRequest::RetargetBranch {
                name: "scratch".to_string(),
                origin: ROOT.to_string(),
            }
        );
        assert_eq!(parsed("/branches/list"), ControlRequest::ListBranches);
        assert_eq!(
            parse_request("/branches/list", "ignored body").unwrap(),
            ControlRequest::ListBranches,
            "a verb that takes nothing ignores the body"
        );
    }

    /// A segment that is not a branch name, and a path of the wrong shape, name
    /// no verb.
    #[test]
    fn a_path_naming_no_verb_is_not_found() {
        for url in [
            "/diff/",
            "/diff/a.b",
            "/reload/a/b",
            "/branch",
            "/branch/",
            "/branch/a b",
            "/branch/a/from",
            "/branch/a/from/",
            "/branch/a/rename/b",
            "/branch/a/retarget",
            "/branches",
            "/branches/all",
            "/nope",
        ] {
            assert_eq!(status_of(url, "x"), 404, "{url}");
        }
    }

    #[test]
    fn an_unserviced_message_unblocks_its_caller() {
        let (tx, rx) = sync_channel::<ControlReply>(0);
        let waiter = thread::spawn(move || rx.recv().expect("a reply").status);
        drop(ControlMessage {
            request: ControlRequest::Reload {
                branch: ROOT.to_string(),
                code: "x".to_string(),
            },
            reply: Some(tx),
        });
        assert_eq!(waiter.join().unwrap(), 503);
    }
}
