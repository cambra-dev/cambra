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
//! | `/branch/<name>/info` | nothing | Report `<name>`'s origin, versions and source |
//! | `/branches` | nothing | List every branch |
//!
//! `/reload` and both `/branch` forms that change the table require `POST`,
//! and any other method answers 405. An omitted `<branch>` or `<parent>`
//! means `main`. A segment in a name position that is not a branch name is an
//! unknown path, and answers 404.
//!
//! The source may be the whole query string, percent-decoded, or a `POST` body.
//! The query form is percent-encoded rather than form-encoded: `+` stands for
//! itself, because it is addition and string concatenation in CHL (see
//! [`percent_decode`]).
//! A `phase=` parameter selects where in the pipeline `/diff` compares (see
//! [`OFFERED_PHASES`]); it must come first when the query also carries the
//! source.
//!
//! # Who may send a request
//!
//! A `/reload` runs the code it carries, so [`admit`] refuses every request a
//! web page could have sent. The port serves no page, and its clients are
//! `curl`, scripts and editors, none of which sends the headers a browser adds:
//!
//! - **`Origin`**, which a browser sends on every `POST` and on a cross-origin
//!   `fetch`. A cross-site page can `POST` a `text/plain` body with no
//!   preflight, so binding loopback alone does not keep it out.
//! - **`Sec-Fetch-Site`** other than `none`, which a browser sends on a request
//!   that carries no `Origin`, such as an `<img>` loading a `/diff` URL. `none`
//!   is the reader typing the URL into the address bar.
//! - **A `Host` that does not name loopback.** A page on a name its attacker
//!   re-points at `127.0.0.1` is same-origin with the port, and its same-origin
//!   `GET` carries no `Origin` in a browser that predates `Sec-Fetch-Site`.
//!
//! # Why requests are handed to the main loop
//!
//! Nothing on the interpreter side is [`Send`]: the operator graph, the sources,
//! and the compilation contexts are `Rc`/`RefCell` throughout, and compiling a
//! new version needs all three. So the server thread does no compilation. It
//! parses the request into a [`ControlRequest`], sends it to the main loop over
//! a channel, and blocks on the reply — the main loop services it between ticks,
//! where it already holds the program exclusively.

use std::sync::mpsc::{Receiver, SendError, SyncSender, sync_channel};
use std::thread;

use crate::ccl::context::{CompileError, GlobalContext, Phase, ReuseTally};
use crate::ccl::load::{LoadError, LoadedProgram};
use crate::live_program::{
    BranchError, LiveProgram, MAIN_BRANCH, MainConsumerFactory, ReloadError, ReloadReport,
    is_branch_name, render_unreadable,
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
    /// Report `name`'s branch origin, versions and current source.
    Info { name: String },
    /// List every branch.
    List,
}

impl ControlRequest {
    /// Whether the request changes what a branch runs or what the table holds,
    /// which is what makes it require `POST`.
    pub fn mutates(&self) -> bool {
        match self {
            ControlRequest::Reload { .. }
            | ControlRequest::Branch { .. }
            | ControlRequest::Delete { .. } => true,
            ControlRequest::Diff { .. }
            | ControlRequest::DiffBranches { .. }
            | ControlRequest::Info { .. }
            | ControlRequest::List => false,
        }
    }
}

/// Refuse a mutating request sent with any method but `POST`, so a browser
/// prefetch or a stray `GET` cannot reload, create or delete a branch.
fn require_post(method: &str, request: &ControlRequest) -> Result<(), ControlReply> {
    if request.mutates() && !method.eq_ignore_ascii_case("POST") {
        return Err(ControlReply {
            status: 405,
            body: format!("{method} cannot change a branch; send POST\n"),
        });
    }
    Ok(())
}

/// Whether a request with these headers may reach the control port; see the
/// module docs, "Who may send a request".
pub fn admit(
    host: Option<&str>,
    origin: Option<&str>,
    fetch_site: Option<&str>,
) -> Result<(), ControlReply> {
    if !host.is_some_and(is_loopback_host) {
        return Err(ControlReply {
            status: 403,
            body: format!(
                "the Host header {} does not name loopback\n",
                host.map_or("(absent)".to_string(), |h| format!("`{h}`"))
            ),
        });
    }
    if let Some(origin) = origin {
        return Err(ControlReply {
            status: 403,
            body: format!("a page at `{origin}` cannot use the control port\n"),
        });
    }
    if let Some(site) = fetch_site
        && !site.eq_ignore_ascii_case("none")
    {
        return Err(ControlReply {
            status: 403,
            body: format!("a {site} browser request cannot use the control port\n"),
        });
    }
    Ok(())
}

/// Whether a `Host` header names this machine's loopback: `localhost`, a name
/// under `.localhost`, or a loopback address, with or without a port.
pub fn is_loopback_host(host: &str) -> bool {
    let name = if let Some(bracketed) = host.strip_prefix('[') {
        match bracketed.split_once(']') {
            Some((address, _)) => address,
            None => return false,
        }
    } else {
        match host.rsplit_once(':') {
            Some((name, port)) if port.bytes().all(|b| b.is_ascii_digit()) => name,
            _ => host,
        }
    };
    let name = name.to_ascii_lowercase();
    name == "localhost"
        || name.ends_with(".localhost")
        || name
            .parse::<std::net::IpAddr>()
            .is_ok_and(|ip| ip.is_loopback())
}

/// The value of the header `name` on `request`, if it carries one.
pub fn header_value(request: &tiny_http::Request, name: &str) -> Option<String> {
    request
        .headers()
        .iter()
        .find(|h| h.field.as_str().as_str().eq_ignore_ascii_case(name))
        .map(|h| h.value.as_str().to_string())
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

/// The label a posted version's diagnostics carry: the text arrived over the
/// control port and need not match any file on disk.
const POSTED: &str = "<new>";

/// The reply to a branch operation that did nothing: `404` for a name the
/// table does not hold, `400` for a refusal or a compile error. `posted` is the
/// version the request carried, which a compile error's spans point into.
fn branch_error(error: BranchError, posted: &LoadedProgram) -> ControlReply {
    match error {
        BranchError::Unknown(name) => {
            ControlReply::not_found(format!("no branch named `{name}`\n"))
        }
        BranchError::Refused(why) => ControlReply::rejected(why),
        BranchError::Reload(e) => ControlReply::rejected(posted_rejection(&e, posted)),
    }
}

/// The text refusing a posted version.
///
/// A posted version is its root file alone, so a version naming a module that
/// is not under the std root fails to load it. The reply says so, since the
/// same version read from disk would find the module's file.
fn posted_rejection(error: &ReloadError, posted: &LoadedProgram) -> String {
    let mut reply = error.render(posted.sources());
    let names_a_module = matches!(error, ReloadError::Compile(errs) if errs
        .iter()
        .any(|e| matches!(e, CompileError::Load(LoadError::Missing { .. }))));
    if names_a_module {
        reply.push_str(
            "note: a posted version is a single file, so a program of several modules cannot \
             be reloaded yet\n",
        );
    }
    reply
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
        } => {
            let posted = LoadedProgram::from_text(POSTED, code.as_str());
            match live.diff_against(ctx, branch, &posted, *phase) {
                Ok(report) => ControlReply::ok(format!(
                    "{}{}",
                    report.diff,
                    render_unreadable(&report.unreadable)
                )),
                Err(e) => branch_error(e, &posted),
            }
        }
        ControlRequest::DiffBranches { from, to, phase } => {
            match live.diff_between(ctx, from, to, *phase) {
                Ok(diff) => ControlReply::ok(diff),
                // Both versions are running ones, so `diff_between` renders a
                // compile error in either against its own map, and nothing
                // posted is rendered against.
                Err(e) => branch_error(e, &LoadedProgram::from_text(POSTED, "")),
            }
        }
        // A rebuilt operator's producer takes the scheduler's probe slot when it
        // is built, as the first compile's did; a created branch's do too.
        ControlRequest::Reload { branch, code } => {
            let posted = LoadedProgram::from_text(POSTED, code.as_str());
            match live.reload(ctx, branch, &posted, main_consumer) {
                Ok(report) => ControlReply::ok(render_reload(&report)),
                Err(e) => branch_error(e, &posted),
            }
        }
        ControlRequest::Branch { name, parent, code } => {
            let posted = LoadedProgram::from_text(POSTED, code.as_str());
            match live.create_branch(ctx, name, parent, &posted, main_consumer) {
                Ok(created) => ControlReply::ok(format!(
                    "created `{}@{}` from `{}`\n{}",
                    created.name,
                    created.version,
                    created.from,
                    render_reload(&created.report),
                )),
                Err(e) => branch_error(e, &posted),
            }
        }
        ControlRequest::Delete { name } => match live.delete_branch(ctx, name) {
            Ok(_) => ControlReply::ok(format!("deleted branch `{name}`\n")),
            Err(e) => branch_error(e, &LoadedProgram::from_text(POSTED, "")),
        },
        ControlRequest::Info { name } => match live.render_info(name) {
            Ok(info) => ControlReply::ok(info),
            Err(e) => branch_error(e, &LoadedProgram::from_text(POSTED, "")),
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

/// Bind the control port on loopback.
///
/// Loopback, not `0.0.0.0`: a `/reload` replaces the running program with
/// whatever source it carries, so any host that can reach the port can run code
/// in the process. Reaching it from another host is a port-forward, as for the
/// inspector's port (`docs/inspector.md`, "Running it").
fn bind(port: u16) -> Result<tiny_http::Server, Box<dyn std::error::Error + Send + Sync>> {
    tiny_http::Server::http(format!("127.0.0.1:{port}"))
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
        let server = bind(port)?;
        // The port bound, not the one asked for: they differ under
        // `--control=0`, where the OS picks a free port, and printing `0` would
        // leave nothing able to send to it. Printed rather than logged for the
        // same reason: a log line is hidden unless `RUST_LOG` asks for it.
        let port = server
            .server_addr()
            .to_ip()
            .map_or(port, |addr| addr.port());
        eprintln!("cambra: control port at http://localhost:{port}");

        thread::spawn(move || {
            for mut request in server.incoming_requests() {
                let mut body = String::new();
                let _ = std::io::Read::read_to_string(request.as_reader(), &mut body);
                let parsed = admit(
                    header_value(&request, "Host").as_deref(),
                    header_value(&request, "Origin").as_deref(),
                    header_value(&request, "Sec-Fetch-Site").as_deref(),
                )
                .and_then(|()| parse_request(request.url(), &body))
                .and_then(|parsed| {
                    require_post(request.method().as_str(), &parsed).map(|()| parsed)
                });
                let reply = match parsed {
                    Err(reply) => reply,
                    Ok(parsed) => {
                        let (reply_tx, reply_rx) = sync_channel::<ControlReply>(0);
                        let message = ControlMessage {
                            request: parsed,
                            reply: Some(reply_tx),
                        };
                        // A closed reply channel means the main loop dropped the
                        // message without the `Drop` answer arriving, which is a
                        // bug rather than a state to report differently.
                        match tx.send(message) {
                            // A closed channel means the driver loop has ended,
                            // which it does when the program finishes; under
                            // `--inspect` the binary goes on serving. The unsent
                            // message is disarmed first: its `Drop` answer would
                            // send on `reply_tx`, whose receiver is this thread's
                            // own `reply_rx`, and the zero-capacity send would
                            // wait for it forever.
                            Err(SendError(mut unsent)) => {
                                unsent.reply = None;
                                ControlReply {
                                    status: 409,
                                    body: "the program has finished, and a finished program \
                                           takes no control request\n"
                                        .to_string(),
                                }
                            }
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

/// The `phase=` spelling that names `phase`, or `None` for a phase `/diff`
/// does not offer.
pub fn phase_spelling(phase: Phase) -> Option<&'static str> {
    OFFERED_PHASES
        .iter()
        .find(|(_, offered)| *offered == phase)
        .map(|(spelling, _)| *spelling)
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
/branch/<name>/info, /branches\n";

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
                branch: rest.first().copied().unwrap_or(MAIN_BRANCH).to_string(),
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
                branch: rest.first().copied().unwrap_or(MAIN_BRANCH).to_string(),
                code,
            })
        }
        ("branch", [name]) => {
            require_code(&code)?;
            Ok(ControlRequest::Branch {
                name: name.to_string(),
                parent: MAIN_BRANCH.to_string(),
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
        ("branches", []) => Ok(ControlRequest::List),
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

    /// What `curl` and a script send: a loopback `Host`, and no browser header.
    #[test]
    fn a_request_without_browser_headers_is_admitted() {
        for host in ["127.0.0.1:8081", "localhost:8081", "[::1]:8081"] {
            assert!(admit(Some(host), None, None).is_ok(), "{host}");
        }
        // The reader typing a `/branches` URL into the address bar.
        assert!(admit(Some("localhost:8081"), None, Some("none")).is_ok());
    }

    /// A cross-site `POST` of a `text/plain` body needs no preflight, so the
    /// `Origin` it carries is what refuses it.
    #[test]
    fn a_request_carrying_an_origin_is_refused() {
        for origin in ["http://example.com", "http://localhost:8081", "null"] {
            let refusal = admit(Some("localhost:8081"), Some(origin), None).unwrap_err();
            assert_eq!(refusal.status, 403, "{origin}");
        }
    }

    /// An `<img>` or `<script>` loading a control-port URL sends no `Origin`.
    #[test]
    fn a_browser_request_from_a_page_is_refused() {
        for site in ["cross-site", "same-site", "same-origin"] {
            let refusal = admit(Some("localhost:8081"), None, Some(site)).unwrap_err();
            assert_eq!(refusal.status, 403, "{site}");
        }
    }

    /// The DNS-rebinding shape: a same-origin request to a name re-pointed at
    /// loopback.
    #[test]
    fn a_host_that_does_not_name_loopback_is_refused() {
        assert_eq!(
            admit(Some("rebind.example:8081"), None, None)
                .unwrap_err()
                .status,
            403
        );
        assert_eq!(admit(None, None, None).unwrap_err().status, 403);
    }

    #[test]
    fn loopback_hosts_are_recognised_with_and_without_a_port() {
        for host in [
            "localhost",
            "localhost:8080",
            "LOCALHOST:8080",
            "app.localhost:3000",
            "127.0.0.1",
            "127.0.0.1:8080",
            "127.1.2.3:80",
            "[::1]",
            "[::1]:8080",
        ] {
            assert!(is_loopback_host(host), "{host}");
        }
        for host in [
            "example.com",
            "localhost.example.com:8080",
            "10.0.0.1:8080",
            "[::2]:8080",
            "0.0.0.0:8080",
            "[::1",
        ] {
            assert!(!is_loopback_host(host), "{host}");
        }
    }

    /// The control port answers loopback only, because a `/reload` runs the
    /// code it carries.
    #[test]
    fn the_control_port_binds_loopback() {
        let server = bind(0).expect("binding an ephemeral port");
        let addr = server.server_addr().to_ip().expect("an ip address");
        assert!(addr.ip().is_loopback(), "bound {addr}, not loopback");
    }

    /// A posted version naming a module is refused with the reason the module
    /// has no file: a posted version is one file.
    #[test]
    fn a_posted_version_naming_a_module_says_it_is_one_file() {
        use crate::ccl::context::compile_to;
        let note = "a program of several modules cannot be reloaded yet";
        let reject = |code: &str| {
            let posted = LoadedProgram::from_text(POSTED, code);
            let errors = compile_to(&posted, Phase::Lower).unwrap_err();
            posted_rejection(&ReloadError::Compile(errors), &posted)
        };
        let reply = reject("import catalog\n1\n");
        assert!(reply.contains("no module `catalog`"), "{reply}");
        assert!(reply.contains(note), "{reply}");
        let reply = reject("x = = 1\n");
        assert!(!reply.contains(note), "{reply}");
    }

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
                branch: MAIN_BRANCH.to_string(),
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
        assert_eq!(parsed("/branches"), ControlRequest::List);
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
        assert_eq!(status_of("/branches/list"), 404);
        assert_eq!(status_of("/nonsense"), 404);
    }

    /// A verb that changes a branch or the table requires `POST`; one that only
    /// reads accepts any method.
    #[test]
    fn only_post_may_change_a_branch() {
        let delete = parse_request("/branch/qa/delete", "").expect("parses");
        assert_eq!(
            require_post("GET", &delete).expect_err("refused").status,
            405
        );
        assert!(require_post("POST", &delete).is_ok());
        let reload = parse_request("/reload", "x = 1; x").expect("parses");
        assert_eq!(
            require_post("GET", &reload).expect_err("refused").status,
            405
        );
        let create = parse_request("/branch/qa", "x = 1; x").expect("parses");
        assert_eq!(
            require_post("PUT", &create).expect_err("refused").status,
            405
        );
        for read in ["/branches", "/branch/qa/info", "/diff/a/b"] {
            let request = parse_request(read, "").expect("parses");
            assert!(require_post("GET", &request).is_ok(), "{read} only reads");
        }
    }

    /// The sourceless verbs ignore the request body.
    #[test]
    fn delete_info_and_list_ignore_the_body() {
        assert_eq!(
            parse_request("/branch/qa/delete", "x = 1; x").expect("parses"),
            ControlRequest::Delete { name: "qa".into() }
        );
        assert_eq!(
            parse_request("/branches", "x = 1; x").expect("parses"),
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
