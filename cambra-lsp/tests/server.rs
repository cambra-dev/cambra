//! The server end to end, through `lsp-server`'s in-memory connection
//! (`cambra-lsp/design-cambra-lsp.md`, "Testing").
//!
//! - Protocol behavior: the handshake, the encoding check, shutdown and exit,
//!   requests the server does not handle.
//! - Goldens: the diagnostics, outline and folding ranges of every `.cambra`
//!   file under the repository's `tests/` and `editors/`, and of the lexer
//!   recovery corpus. `CAMBRA_BLESS=1` rewrites them.

use cambra_lsp::Ended;
use indoc::indoc;
use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use serde_json::{Value, json};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::thread::JoinHandle;
use std::time::Duration;

/// A client connected to a server on its own thread.
struct TestServer {
    client: Connection,
    server: Option<JoinHandle<Result<Ended, String>>>,
    next_id: i32,
    /// Notifications read while waiting for something else.
    unread: Vec<Notification>,
}

const TIMEOUT: Duration = Duration::from_secs(10);

impl TestServer {
    /// A server initialized by a client offering `encodings`.
    fn with_encodings(encodings: &[&str]) -> (TestServer, Response) {
        let (server, client) = Connection::memory();
        let handle =
            std::thread::spawn(move || cambra_lsp::run(&server).map_err(|e| e.to_string()));
        let mut test = TestServer {
            client,
            server: Some(handle),
            next_id: 0,
            unread: Vec::new(),
        };
        let response = test.request_raw(
            "initialize",
            json!({"capabilities": {"general": {"positionEncodings": encodings}}}),
        );
        (test, response)
    }

    fn new() -> TestServer {
        let (test, response) = TestServer::with_encodings(&["utf-8", "utf-16"]);
        let result = response.response_result.expect("initialize succeeds");
        assert_eq!(result["capabilities"]["positionEncoding"], json!("utf-8"));
        test.notify("initialized", json!({}));
        test
    }

    fn notify(&self, method: &str, params: Value) {
        self.client
            .sender
            .send(Notification::new(method.to_owned(), params).into())
            .expect("the server is listening");
    }

    fn request_raw(&mut self, method: &str, params: Value) -> Response {
        self.next_id += 1;
        let id = RequestId::from(self.next_id);
        self.client
            .sender
            .send(Request::new(id.clone(), method.to_owned(), params).into())
            .expect("the server is listening");
        loop {
            match self.recv() {
                Message::Response(response) if response.id == id => return response,
                Message::Notification(n) => self.unread.push(n),
                other => panic!("expected the response to {method}, got {other:?}"),
            }
        }
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        self.request_raw(method, params)
            .response_result
            .unwrap_or_else(|e| panic!("{method} failed: {e:?}"))
    }

    fn recv(&self) -> Message {
        self.client
            .receiver
            .recv_timeout(TIMEOUT)
            .expect("the server answers within the timeout")
    }

    /// The diagnostics published for `uri` at `version`, skipping any
    /// published for earlier versions.
    fn diagnostics(&mut self, uri: &str, version: i64) -> Value {
        loop {
            let n = match self.unread.iter().position(|n| is_publish(n, uri, version)) {
                Some(i) => self.unread.remove(i),
                None => match self.recv() {
                    Message::Notification(n) => n,
                    other => panic!("expected diagnostics for {uri}, got {other:?}"),
                },
            };
            if is_publish(&n, uri, version) {
                return n.params["diagnostics"].clone();
            }
            self.unread.push(n);
        }
    }

    fn open(&self, uri: &str, text: &str) {
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": uri, "languageId": "cambra", "version": 1, "text": text}}),
        );
    }

    /// Shuts the server down and returns how its session ended.
    fn shutdown(mut self) -> Ended {
        let response = self.request_raw("shutdown", Value::Null);
        assert!(response.response_result.is_ok(), "{response:?}");
        self.exit()
    }

    fn exit(mut self) -> Ended {
        self.notify("exit", Value::Null);
        let ended = self
            .server
            .take()
            .expect("the server is running")
            .join()
            .expect("the server thread does not panic")
            .expect("the session ends without error");
        // Diagnostics superseded by a later publish need no reading; anything
        // else unread is a message a test missed.
        let rest: Vec<Message> = self.client.receiver.try_iter().collect();
        let unread: Vec<&Notification> = self
            .unread
            .iter()
            .chain(rest.iter().filter_map(|m| match m {
                Message::Notification(n) => Some(n),
                _ => None,
            }))
            .filter(|n| n.method != "textDocument/publishDiagnostics")
            .collect();
        assert!(unread.is_empty(), "unread messages: {unread:?}");
        assert!(
            rest.iter().all(|m| matches!(m, Message::Notification(_))),
            "unread responses: {rest:?}"
        );
        ended
    }
}

fn is_publish(n: &Notification, uri: &str, version: i64) -> bool {
    n.method == "textDocument/publishDiagnostics"
        && n.params["uri"] == json!(uri)
        && n.params["version"] == json!(version)
}

#[test]
fn a_session_ends_cleanly_after_shutdown_then_exit() {
    assert_eq!(TestServer::new().shutdown(), Ended::Shutdown);
}

#[test]
fn exit_without_shutdown_is_reported() {
    assert_eq!(TestServer::new().exit(), Ended::WithoutShutdown);
}

#[test]
fn requests_after_shutdown_are_refused() {
    let mut server = TestServer::new();
    server.request("shutdown", Value::Null);
    let response = server.request_raw(
        "textDocument/foldingRange",
        json!({"textDocument": {"uri": "file:///a.cambra"}}),
    );
    let error = response.response_result.expect_err("refused");
    assert_eq!(error.code, lsp_server::ErrorCode::InvalidRequest as i32);
    assert_eq!(server.exit(), Ended::Shutdown);
}

#[test]
fn a_client_without_utf8_is_refused() {
    let (server, response) = TestServer::with_encodings(&["utf-16"]);
    let error = response.response_result.expect_err("initialize fails");
    assert!(error.message.contains("Neovim 0.11"), "{error:?}");
    let ended = server.server.expect("spawned").join().expect("no panic");
    assert!(ended.is_err(), "{ended:?}");
}

#[test]
fn an_unhandled_request_is_method_not_found() {
    let mut server = TestServer::new();
    let response = server.request_raw("textDocument/hover", json!({}));
    let error = response.response_result.expect_err("not handled");
    assert_eq!(error.code, lsp_server::ErrorCode::MethodNotFound as i32);
    server.shutdown();
}

/// An incremental edit lands in the server's text: fixing the unclosed
/// bracket clears the diagnostic.
#[test]
fn an_incremental_edit_updates_the_diagnostics() {
    let mut server = TestServer::new();
    let uri = "file:///a.cambra";
    server.open(uri, "x = f(1\ny = 2\n");
    assert_eq!(server.diagnostics(uri, 1).as_array().map(Vec::len), Some(1));
    server.notify(
        "textDocument/didChange",
        json!({
            "textDocument": {"uri": uri, "version": 2},
            "contentChanges": [{"range": {"start": {"line": 0, "character": 7}, "end": {"line": 0, "character": 7}}, "text": ")"}],
        }),
    );
    assert_eq!(server.diagnostics(uri, 2), json!([]));
    server.shutdown();
}

/// A mismatched close bracket links to the open bracket it names.
#[test]
fn a_mismatched_close_links_its_open_bracket() {
    let mut server = TestServer::new();
    let uri = "file:///a.cambra";
    server.open(
        uri,
        indoc! {"
        x = f(a]
        y = 2
    "},
    );
    let diagnostics = server.diagnostics(uri, 1);
    assert_eq!(diagnostics[0]["message"], json!("`]` does not match `(`"));
    let related = &diagnostics[0]["relatedInformation"][0];
    assert_eq!(related["message"], json!("this bracket is never closed"));
    assert_eq!(
        related["location"]["range"]["start"],
        json!({"line": 0, "character": 5})
    );
    server.shutdown();
}

// ---- Goldens ---------------------------------------------------------------

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// The `.cambra` files under `dir`, recursively, sorted.
fn cambra_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n == "node_modules") {
                    continue;
                }
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "cambra") {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// A protocol range as 1-based `line:col-line:col`.
fn range(r: &Value) -> String {
    let pos = |p: &Value| {
        format!(
            "{}:{}",
            p["line"].as_u64().unwrap() + 1,
            p["character"].as_u64().unwrap() + 1
        )
    };
    format!("{}-{}", pos(&r["start"]), pos(&r["end"]))
}

fn render_symbols(out: &mut String, symbols: &Value, depth: usize) {
    for symbol in symbols.as_array().into_iter().flatten() {
        // `SymbolKind` numbers: 2 Module, 12 Function, 13 Variable.
        let kind = match symbol["kind"].as_u64() {
            Some(2) => "module",
            Some(12) => "function",
            Some(13) => "variable",
            other => panic!("an unexpected symbol kind {other:?}"),
        };
        writeln!(
            out,
            "  {:indent$}{kind} {} {} (name {})",
            "",
            symbol["name"].as_str().unwrap(),
            range(&symbol["range"]),
            range(&symbol["selectionRange"]),
            indent = depth * 2,
        )
        .unwrap();
        render_symbols(out, &symbol["children"], depth + 1);
    }
}

/// The golden rendering of one file: its diagnostics, outline and folds.
fn render(server: &mut TestServer, uri: &str, text: &str) -> String {
    server.open(uri, text);
    let mut out = String::from("diagnostics:\n");
    for d in server.diagnostics(uri, 1).as_array().unwrap() {
        writeln!(
            out,
            "  {} {}",
            range(&d["range"]),
            d["message"].as_str().unwrap()
        )
        .unwrap();
        for r in d["relatedInformation"].as_array().into_iter().flatten() {
            writeln!(
                out,
                "    {} {}",
                range(&r["location"]["range"]),
                r["message"].as_str().unwrap()
            )
            .unwrap();
        }
    }
    out.push_str("symbols:\n");
    let symbols = server.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri}}),
    );
    render_symbols(&mut out, &symbols, 0);
    out.push_str("folds:\n");
    let folds = server.request(
        "textDocument/foldingRange",
        json!({"textDocument": {"uri": uri}}),
    );
    for fold in folds.as_array().unwrap() {
        let kind = fold["kind"]
            .as_str()
            .map(|k| format!(" {k}"))
            .unwrap_or_default();
        writeln!(
            out,
            "  {}-{}{kind}",
            fold["startLine"].as_u64().unwrap() + 1,
            fold["endLine"].as_u64().unwrap() + 1
        )
        .unwrap();
    }
    server.notify(
        "textDocument/didClose",
        json!({"textDocument": {"uri": uri}}),
    );
    out
}

/// Renders every file in `files` into one golden at `golden`, each section
/// headed by the file's path from the repository root.
fn check_golden(files: &[PathBuf], golden: &str) {
    let root = repo_root().canonicalize().unwrap();
    let mut server = TestServer::new();
    let mut rendered = String::new();
    for path in files {
        let path = path.canonicalize().unwrap();
        let name = path.strip_prefix(&root).unwrap().display().to_string();
        let text = std::fs::read_to_string(&path).unwrap();
        let uri = format!("file:///{name}");
        writeln!(rendered, "== {name}").unwrap();
        rendered.push_str(&render(&mut server, &uri, &text));
    }
    server.shutdown();
    let golden_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/goldens")
        .join(golden);
    if std::env::var_os("CAMBRA_BLESS").is_some() {
        std::fs::create_dir_all(golden_path.parent().unwrap()).unwrap();
        std::fs::write(&golden_path, &rendered).unwrap();
    }
    let expected = std::fs::read_to_string(&golden_path).unwrap_or_default();
    assert!(
        rendered == expected,
        "{} differs; if the change is intended, re-run with CAMBRA_BLESS=1 and review its diff",
        golden_path.display()
    );
}

#[test]
fn repository_programs_match_their_golden() {
    let root = repo_root();
    let mut files = cambra_files(&root.join("tests"));
    files.extend(cambra_files(&root.join("editors")));
    assert!(!files.is_empty());
    check_golden(&files, "programs.txt");
}

#[test]
fn lexer_recovery_corpus_matches_its_golden() {
    let files = cambra_files(&repo_root().join("chl-parser/tests/lexer_recovery"));
    assert!(!files.is_empty());
    check_golden(&files, "lexer_recovery.txt");
}
