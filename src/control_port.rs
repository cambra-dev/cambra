//! Control port: HTTP endpoints for diffing, reloading, creating, deleting and
//! listing the branches of a running program — see
//! `src/ccl/design/program-evolution.md`, "The control port".
//!
//! | Verb | Takes | Does |
//! | --- | --- | --- |
//! | `/diff[/<branch>]` | `[phase=<p>&]<source>` | How `<source>` differs from the branch's current version |
//! | `/diff/<a>/<b>` | `[phase=<p>]` | How `<b>`'s current version differs from `<a>`'s |
//! | `/reload[/<branch>]` | `<source>` | Replace the branch's version with `<source>` |
//! | `/branch/<name>[/from/<parent>]` | `<source>` | Create `<name>` from `<parent>` and reload it with `<source>` |
//! | `/branch/<name>/delete` | nothing | Delete `<name>` |
//! | `/branch/<name>/info` | nothing | Report `<name>`'s provenance, versions and source |
//! | `/branches/list` | nothing | List every branch |
//!
//! An omitted `<branch>` or `<parent>` means `main`. A segment in a name
//! position that is not a branch name is an unknown path, and answers 404.
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

use crate::ccl::context::{GlobalContext, Phase, ReuseTally, render_errors};
use crate::live_program::{
    BranchError, LiveProgram, MainConsumerFactory, ROOT, ReloadReport, is_branch_name,
    render_unreadable,
};

/// What a control-port client asked for.
#[derive(Debug, PartialEq)]
pub enum ControlRequest {
    /// Report how `code` differs from `branch`'s current version, comparing at
    /// `phase`.
    Diff {
        branch: String,
        code: String,
        phase: Phase,
    },
    /// Report how `to`'s current version differs from `from`'s, comparing at
    /// `phase`.
    DiffBranches {
        from: String,
        to: String,
        phase: Phase,
    },
    /// Replace `branch`'s version with `code`.
    Reload { branch: String, code: String },
    /// Create `name` from `parent`'s current version and reload it with `code`.
    Branch {
        name: String,
        parent: String,
        code: String,
    },
    /// Delete `name`.
    Delete { name: String },
    /// Report `name`'s branch provenance, versions and current source.
    Info { name: String },
    /// List every branch.
    List,
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
    /// for something the branch table refuses.
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

/// A reload's `200` body: the tally, a blank line, the difference at
/// `as-of-read`, and the variables that begin above their loops' inputs.
fn render_reload(report: &ReloadReport) -> String {
    let ReuseTally { kept, bound } = report.reuse;
    format!(
        "reloaded: {kept}/{bound} operators kept\n\n{}{}",
        report.diff,
        render_unreadable(&report.unreadable),
    )
}

/// The reply to a branch operation that did nothing: `404` for a name the
/// table does not hold, `400` for a refusal or a compile error. `code` is the
/// source a compile error's spans point into.
fn branch_error(error: BranchError, code: &str) -> ControlReply {
    match error {
        BranchError::Unknown(name) => {
            ControlReply::not_found(format!("no branch named `{name}`\n"))
        }
        BranchError::Refused(why) => ControlReply::rejected(why),
        BranchError::Compile(errs) => ControlReply::rejected(render_errors(&errs, "<new>", code)),
    }
}

/// Answer `request` against the running branch table.
///
/// The main loop's half of the control port, a library function so a test can
/// drive every verb without a socket. A reload or a creation arms the reloaded
/// branch's `main` output for the driver's next pass
/// ([`LiveProgram::pull_mains`]).
pub fn service(
    request: &ControlRequest,
    ctx: &mut GlobalContext,
    live: &mut LiveProgram,
    main_consumer: MainConsumerFactory<'_>,
) -> ControlReply {
    match request {
        ControlRequest::Diff {
            branch,
            code,
            phase,
        } => match live.diff_branch(ctx, branch, code, *phase) {
            Ok(report) => ControlReply::ok(format!(
                "{}{}",
                report.diff,
                render_unreadable(&report.unreadable)
            )),
            Err(e) => branch_error(e, code),
        },
        ControlRequest::DiffBranches { from, to, phase } => {
            match live.diff_between(ctx, from, to, *phase) {
                Ok(diff) => ControlReply::ok(diff),
                // A compile error here is in a running branch's source, and
                // which of the two it is in is not known here; the rendering
                // names no source text.
                Err(e) => branch_error(e, ""),
            }
        }
        // A rebuilt operator's producer takes the scheduler's probe slot when it
        // is built, as the first compile's did; a created branch's do too.
        ControlRequest::Reload { branch, code } => {
            match live.reload_branch(ctx, branch, code, main_consumer) {
                Ok(report) => ControlReply::ok(render_reload(&report)),
                Err(e) => branch_error(e, code),
            }
        }
        ControlRequest::Branch { name, parent, code } => {
            match live.create_branch(ctx, name, parent, code, main_consumer) {
                Ok(created) => ControlReply::ok(format!(
                    "created `{}@{}` from `{}`\n{}",
                    created.name,
                    created.version,
                    created.from,
                    render_reload(&created.report),
                )),
                Err(e) => branch_error(e, code),
            }
        }
        ControlRequest::Delete { name } => match live.delete_branch(ctx, name) {
            Ok(_) => ControlReply::ok(format!("deleted branch `{name}`\n")),
            Err(e) => branch_error(e, ""),
        },
        ControlRequest::Info { name } => match live.render_info(name) {
            Ok(info) => ControlReply::ok(info),
            Err(e) => branch_error(e, ""),
        },
        ControlRequest::List => ControlReply::ok(live.render_branches()),
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

/// Every verb, for the reply to an unknown path.
const ENDPOINTS: &str = "endpoints: /diff[/<branch>]?<source>, /diff/<branch>/<branch>, \
/reload[/<branch>]?<source>, /branch/<name>[/from/<parent>]?<source>, /branch/<name>/delete, \
/branch/<name>/info, /branches/list\n";

/// The branch names a path's segments after its verb spell, or the `404` for a
/// path that is no verb.
///
/// A segment in a name position that is not a branch name makes the whole path
/// unknown, so it answers `404` rather than being read as some other verb.
fn names<'a>(segments: &[&'a str]) -> Result<Vec<&'a str>, ControlReply> {
    if segments.iter().all(|s| is_branch_name(s)) {
        Ok(segments.to_vec())
    } else {
        Err(ControlReply::not_found(ENDPOINTS))
    }
}

/// Parse a request into the [`ControlRequest`] the main loop services, or the
/// reply to send when it is not one.
fn parse_request(url: &str, body: &str) -> Result<ControlRequest, ControlReply> {
    let (path, query) = split_url(url);
    let segments: Vec<&str> = path.trim_start_matches('/').split('/').collect();
    let (verb, rest) = segments
        .split_first()
        .map_or(("", &[][..]), |(verb, rest)| (*verb, rest));
    // Only `/diff` takes a phase, so only `/diff` peels one. On `/reload` a
    // leading `phase=` is the program's own first characters.
    let (phase_name, rest_of_query) = if verb == "diff" {
        split_phase_param(query)
    } else {
        (None, query)
    };

    // The source is the body when there is one, so a program containing `&` or
    // `#` need not be percent-encoded to survive the query string.
    let code = if body.trim().is_empty() {
        percent_decode(rest_of_query)
    } else {
        body.to_string()
    };
    let phase = || -> Result<Phase, ControlReply> {
        match phase_name {
            None => Ok(DEFAULT_PHASE),
            Some(name) => phase_from_name(name).ok_or_else(|| {
                ControlReply::rejected(format!(
                    "unknown phase {name:?}; expected one of: {}\n",
                    phase_names()
                ))
            }),
        }
    };

    match (verb, names(rest)?.as_slice()) {
        ("diff", [] | [_]) => {
            let phase = phase()?;
            require_code(&code)?;
            Ok(ControlRequest::Diff {
                branch: rest.first().copied().unwrap_or(ROOT).to_string(),
                code,
                phase,
            })
        }
        ("diff", [from, to]) => {
            let phase = phase()?;
            // This verb takes no source, so the body is ignored as the other
            // sourceless verbs ignore theirs. What follows the phase in the query
            // is refused rather than ignored: it reads as a source for a verb
            // that compares two running versions and would take none.
            if !percent_decode(rest_of_query).trim().is_empty() {
                return Err(ControlReply::rejected(
                    "/diff/<branch>/<branch> compares two running versions and takes no source\n",
                ));
            }
            Ok(ControlRequest::DiffBranches {
                from: from.to_string(),
                to: to.to_string(),
                phase,
            })
        }
        ("reload", [] | [_]) => {
            require_code(&code)?;
            Ok(ControlRequest::Reload {
                branch: rest.first().copied().unwrap_or(ROOT).to_string(),
                code,
            })
        }
        ("branch", [name]) => {
            require_code(&code)?;
            Ok(ControlRequest::Branch {
                name: name.to_string(),
                parent: ROOT.to_string(),
                code,
            })
        }
        ("branch", [name, "from", parent]) => {
            require_code(&code)?;
            Ok(ControlRequest::Branch {
                name: name.to_string(),
                parent: parent.to_string(),
                code,
            })
        }
        ("branch", [name, "delete"]) => Ok(ControlRequest::Delete {
            name: name.to_string(),
        }),
        ("branch", [name, "info"]) => Ok(ControlRequest::Info {
            name: name.to_string(),
        }),
        ("branches", ["list"]) => Ok(ControlRequest::List),
        _ => Err(ControlReply::not_found(ENDPOINTS)),
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

    fn parsed(url: &str) -> ControlRequest {
        parse_request(url, "").unwrap_or_else(|r| panic!("{url} did not parse: {r:?}"))
    }

    fn status_of(url: &str) -> u16 {
        parse_request(url, "").err().map_or(200, |r| r.status)
    }

    /// A verb without a branch segment addresses `main`, and one with a segment
    /// addresses that branch.
    #[test]
    fn an_omitted_branch_segment_means_main() {
        assert_eq!(
            parsed("/diff?x"),
            ControlRequest::Diff {
                branch: "main".into(),
                code: "x".into(),
                phase: DEFAULT_PHASE,
            }
        );
        assert_eq!(
            parsed("/reload/staging?x"),
            ControlRequest::Reload {
                branch: "staging".into(),
                code: "x".into(),
            }
        );
        assert_eq!(
            parsed("/branch/staging?x"),
            ControlRequest::Branch {
                name: "staging".into(),
                parent: "main".into(),
                code: "x".into(),
            }
        );
    }

    /// Every branch verb parses to its request, by position: a name that is
    /// also a keyword (`delete`, `from`) is still a name where a name stands.
    #[test]
    fn every_branch_verb_parses_by_position() {
        assert_eq!(
            parsed("/branch/qa/from/staging?x"),
            ControlRequest::Branch {
                name: "qa".into(),
                parent: "staging".into(),
                code: "x".into(),
            }
        );
        assert_eq!(
            parsed("/branch/qa/delete"),
            ControlRequest::Delete { name: "qa".into() }
        );
        assert_eq!(
            parsed("/branch/qa/info"),
            ControlRequest::Info { name: "qa".into() }
        );
        assert_eq!(parsed("/branches/list"), ControlRequest::List);
        assert_eq!(
            parsed("/branch/delete/delete"),
            ControlRequest::Delete {
                name: "delete".into()
            }
        );
        assert_eq!(
            parsed("/diff/main/staging?phase=inferred"),
            ControlRequest::DiffBranches {
                from: "main".into(),
                to: "staging".into(),
                phase: Phase::Infer,
            }
        );
    }

    /// A segment in a name position that is not a branch name is an unknown
    /// path, as is any path that is no verb.
    #[test]
    fn a_malformed_name_or_path_answers_404() {
        assert_eq!(status_of("/branch/no.dots?x"), 404);
        assert_eq!(status_of("/reload/?x"), 404);
        assert_eq!(status_of("/diff/a/b/c?x"), 404);
        assert_eq!(status_of("/branch/a/rename"), 404);
        assert_eq!(status_of("/branches"), 404);
        assert_eq!(status_of("/nonsense"), 404);
    }

    /// The sourceless verbs ignore the request body.
    #[test]
    fn delete_info_and_list_ignore_the_body() {
        assert_eq!(
            parse_request("/branch/qa/delete", "x = 1; x").expect("parses"),
            ControlRequest::Delete { name: "qa".into() }
        );
        assert_eq!(
            parse_request("/branches/list", "x = 1; x").expect("parses"),
            ControlRequest::List
        );
    }

    /// Comparing two branches takes a phase and no source: query text after the
    /// phase is refused, and a creation or reload without a source is too.
    #[test]
    fn a_two_branch_diff_takes_no_source_and_a_creation_needs_one() {
        assert_eq!(status_of("/diff/a/b?x = 1; x"), 400);
        assert_eq!(status_of("/branch/qa"), 400);
        assert_eq!(status_of("/reload/qa"), 400);
    }
}
