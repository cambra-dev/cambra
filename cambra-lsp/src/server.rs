//! The session: initialization, the batched message loop, and shutdown
//! (`cambra-lsp/design-cambra-lsp.md`, "Lifecycle").

use crate::Error;
use crate::document::Document;
use crate::{diagnostics, folding, symbols};
use chl_parser::line_index::Encoding;
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    CancelNotification, CancelParams, DidChangeTextDocumentNotification,
    DidChangeTextDocumentParams, DidCloseTextDocumentNotification, DidCloseTextDocumentParams,
    DidOpenTextDocumentNotification, DidOpenTextDocumentParams, DocumentSymbolParams,
    DocumentSymbolProvider, DocumentSymbolRequest, DocumentSymbolResponse, ExitNotification,
    FoldingRangeParams, FoldingRangeProvider, FoldingRangeRequest, Id, InitializeParams,
    InitializeResult, LogMessageNotification, LogMessageParams, MessageType, PositionEncodingKind,
    PublishDiagnosticsNotification, PublishDiagnosticsParams, ServerCapabilities, ServerInfo,
    ShutdownRequest, TextDocumentSync, TextDocumentSyncKind, TextDocumentSyncOptions, Uri,
};
use lsp_types::{Notification as _, Request as _};
use std::collections::{HashMap, HashSet};

/// How a session ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ended {
    /// The client sent `shutdown` and then `exit`. The process exits with
    /// status 0.
    Shutdown,
    /// The client sent `exit` without `shutdown`, or closed the connection.
    /// The process exits with status 1.
    WithoutShutdown,
}

/// Serves one client on `connection` until it exits: the handshake, then
/// batches of messages until `exit`.
pub fn run(connection: &Connection) -> Result<Ended, Error> {
    let (id, params) = connection.initialize_start()?;
    let params: InitializeParams = serde_json::from_value(params)?;
    let encoding = encoding(&params);
    let result = InitializeResult {
        capabilities: capabilities(encoding),
        server_info: Some(ServerInfo {
            name: "cambra-lsp".to_owned(),
            version: Some(env!("CARGO_PKG_VERSION").to_owned()),
        }),
    };
    connection.initialize_finish(id, serde_json::to_value(result)?)?;

    let mut server = Server {
        connection,
        encoding,
        documents: HashMap::new(),
        shutdown_requested: false,
    };
    loop {
        let Ok(first) = connection.receiver.recv() else {
            return Ok(Ended::WithoutShutdown);
        };
        let mut batch = vec![first];
        batch.extend(connection.receiver.try_iter());
        if let Some(ended) = server.batch(batch)? {
            return Ok(ended);
        }
    }
}

/// The encoding protocol columns count in for this session: UTF-8 when the
/// client offers it, since spans are byte offsets and need no conversion, and
/// otherwise UTF-16. The protocol requires every server to support UTF-16,
/// and a client that offers no encodings means it.
fn encoding(params: &InitializeParams) -> Encoding {
    let offers_utf8 = params
        .capabilities
        .general
        .as_ref()
        .and_then(|general| general.position_encodings.as_ref())
        .is_some_and(|encodings| encodings.contains(&PositionEncodingKind::UTF8));
    if offers_utf8 {
        Encoding::Utf8
    } else {
        Encoding::Utf16
    }
}

fn capabilities(encoding: Encoding) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(match encoding {
            Encoding::Utf8 => PositionEncodingKind::UTF8,
            Encoding::Utf16 => PositionEncodingKind::UTF16,
        }),
        text_document_sync: Some(TextDocumentSync::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::Incremental),
            will_save: None,
            will_save_wait_until: None,
            save: None,
        })),
        document_symbol_provider: Some(DocumentSymbolProvider::Bool(true)),
        folding_range_provider: Some(FoldingRangeProvider::Bool(true)),
        ..ServerCapabilities::default()
    }
}

struct Server<'a> {
    connection: &'a Connection,
    /// What the columns of every position in this session count.
    encoding: Encoding,
    /// The open documents, keyed by the URI the client sent.
    documents: HashMap<Uri, Document>,
    shutdown_requested: bool,
}

impl Server<'_> {
    /// Handles `batch` in order and publishes diagnostics for every document it
    /// changed, once each. Returns how the session ended if the batch holds
    /// `exit`.
    fn batch(&mut self, batch: Vec<Message>) -> Result<Option<Ended>, Error> {
        let cancelled: HashSet<RequestId> = batch
            .iter()
            .filter_map(|message| match message {
                Message::Notification(n) if n.method == CancelNotification::METHOD.as_str() => {
                    serde_json::from_value::<CancelParams>(n.params.clone()).ok()
                }
                _ => None,
            })
            .map(|params| match params.id {
                Id::Int(id) => RequestId::from(id),
                Id::String(id) => RequestId::from(id),
            })
            .collect();
        // Documents changed in this batch, in the order first changed.
        let mut changed: Vec<Uri> = Vec::new();
        for message in batch {
            match message {
                Message::Request(request) if cancelled.contains(&request.id) => {
                    self.respond_err(request.id, ErrorCode::RequestCanceled, "canceled")?;
                }
                Message::Request(request) => self.request(request)?,
                Message::Notification(n) if n.method == ExitNotification::METHOD.as_str() => {
                    return Ok(Some(if self.shutdown_requested {
                        Ended::Shutdown
                    } else {
                        Ended::WithoutShutdown
                    }));
                }
                Message::Notification(n) => self.notification(n, &mut changed)?,
                // The server sends no requests, so no response is awaited.
                Message::Response(_) => {}
            }
        }
        for uri in changed {
            if let Some(doc) = self.documents.get(&uri) {
                let diagnostics = diagnostics::diagnostics(&uri, doc);
                let version = Some(doc.version());
                self.publish(uri, version, diagnostics)?;
            }
        }
        Ok(None)
    }

    fn request(&mut self, request: Request) -> Result<(), Error> {
        if self.shutdown_requested {
            return self.respond_err(
                request.id,
                ErrorCode::InvalidRequest,
                "the server is shutting down",
            );
        }
        let method = request.method.as_str();
        if method == ShutdownRequest::METHOD.as_str() {
            self.shutdown_requested = true;
            return self.respond(Response::new_ok(request.id, ()));
        }
        if method == DocumentSymbolRequest::METHOD.as_str() {
            let Some((id, params)) = self.extract::<DocumentSymbolParams>(request)? else {
                return Ok(());
            };
            let result = self.documents.get(&params.text_document.uri).map(|doc| {
                DocumentSymbolResponse::DocumentSymbolList(symbols::document_symbols(doc))
            });
            return self.respond(Response::new_ok(id, result));
        }
        if method == FoldingRangeRequest::METHOD.as_str() {
            let Some((id, params)) = self.extract::<FoldingRangeParams>(request)? else {
                return Ok(());
            };
            let result = self
                .documents
                .get(&params.text_document.uri)
                .map(folding::folding_ranges);
            return self.respond(Response::new_ok(id, result));
        }
        self.respond_err(
            request.id,
            ErrorCode::MethodNotFound,
            &format!("cambra-lsp does not handle {}", request.method),
        )
    }

    fn notification(&mut self, n: Notification, changed: &mut Vec<Uri>) -> Result<(), Error> {
        if self.shutdown_requested {
            return Ok(());
        }
        let method = n.method.clone();
        let method = method.as_str();
        if method == DidOpenTextDocumentNotification::METHOD.as_str() {
            let Some(params) = self.params::<DidOpenTextDocumentParams>(n)? else {
                return Ok(());
            };
            let item = params.text_document;
            if self.documents.contains_key(&item.uri) {
                self.log(
                    MessageType::Warning,
                    format!("{} was opened twice", item.uri),
                )?;
            }
            self.documents.insert(
                item.uri.clone(),
                Document::new(item.text, item.version, self.encoding),
            );
            mark_changed(changed, item.uri);
        } else if method == DidChangeTextDocumentNotification::METHOD.as_str() {
            let Some(params) = self.params::<DidChangeTextDocumentParams>(n)? else {
                return Ok(());
            };
            let uri = params.text_document.text_document_identifier.uri;
            let Some(doc) = self.documents.get_mut(&uri) else {
                return self.log(
                    MessageType::Warning,
                    format!("{uri} changed but is not open"),
                );
            };
            let mut skipped = Vec::new();
            for change in params.content_changes {
                if let Err(why) = doc.apply(change) {
                    skipped.push(why);
                }
            }
            doc.set_version(params.text_document.version);
            mark_changed(changed, uri.clone());
            for why in skipped {
                self.log(
                    MessageType::Error,
                    format!("skipped an edit to {uri}, so the server's text now differs from the editor's: {why}"),
                )?;
            }
        } else if method == DidCloseTextDocumentNotification::METHOD.as_str() {
            let Some(params) = self.params::<DidCloseTextDocumentParams>(n)? else {
                return Ok(());
            };
            let uri = params.text_document.uri;
            self.documents.remove(&uri);
            changed.retain(|other| *other != uri);
            self.publish(uri, None, Vec::new())?;
        }
        // `initialized`, `$/cancelRequest` (read at the start of the batch),
        // and notifications the server does not handle need no action.
        Ok(())
    }

    fn publish(
        &self,
        uri: Uri,
        version: Option<i32>,
        diagnostics: Vec<lsp_types::Diagnostic>,
    ) -> Result<(), Error> {
        self.notify(
            PublishDiagnosticsNotification::METHOD.as_str(),
            PublishDiagnosticsParams {
                uri,
                version,
                diagnostics,
            },
        )
    }

    fn log(&self, kind: MessageType, message: String) -> Result<(), Error> {
        self.notify(
            LogMessageNotification::METHOD.as_str(),
            LogMessageParams { kind, message },
        )
    }

    fn notify(&self, method: &str, params: impl serde::Serialize) -> Result<(), Error> {
        self.connection
            .sender
            .send(Notification::new(method.to_owned(), params).into())?;
        Ok(())
    }

    fn respond(&self, response: Response) -> Result<(), Error> {
        self.connection.sender.send(response.into())?;
        Ok(())
    }

    fn respond_err(&self, id: RequestId, code: ErrorCode, message: &str) -> Result<(), Error> {
        self.respond(Response::new_err(id, code as i32, message.to_owned()))
    }

    /// The request's id and parameters, or `None` after answering a request
    /// whose parameters do not parse with `InvalidParams`.
    fn extract<P: serde::de::DeserializeOwned>(
        &self,
        request: Request,
    ) -> Result<Option<(RequestId, P)>, Error> {
        match serde_json::from_value(request.params) {
            Ok(params) => Ok(Some((request.id, params))),
            Err(e) => {
                self.respond_err(request.id, ErrorCode::InvalidParams, &e.to_string())?;
                Ok(None)
            }
        }
    }

    /// The notification's parameters, or `None` after logging parameters that
    /// do not parse. A malformed notification does not end the session.
    fn params<P: serde::de::DeserializeOwned>(&self, n: Notification) -> Result<Option<P>, Error> {
        match serde_json::from_value(n.params) {
            Ok(params) => Ok(Some(params)),
            Err(e) => {
                self.log(MessageType::Error, format!("malformed {}: {e}", n.method))?;
                Ok(None)
            }
        }
    }
}

fn mark_changed(changed: &mut Vec<Uri>, uri: Uri) {
    if !changed.contains(&uri) {
        changed.push(uri);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    const URI: &str = "file:///a.cambra";

    fn notification(method: &str, params: Value) -> Message {
        Notification::new(method.to_owned(), params).into()
    }

    fn open(text: &str) -> Message {
        notification(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": URI, "languageId": "cambra", "version": 1, "text": text}}),
        )
    }

    fn change(version: i32, text: &str) -> Message {
        notification(
            "textDocument/didChange",
            json!({"textDocument": {"uri": URI, "version": version}, "contentChanges": [{"text": text}]}),
        )
    }

    fn symbols_request(id: i32) -> Message {
        Request::new(
            RequestId::from(id),
            "textDocument/documentSymbol".to_owned(),
            json!({"textDocument": {"uri": URI}}),
        )
        .into()
    }

    /// Runs `batch` on a fresh server and returns what it sent.
    fn run_batch(batch: Vec<Message>) -> Vec<Message> {
        let (server, client) = Connection::memory();
        let mut s = Server {
            connection: &server,
            encoding: Encoding::Utf8,
            documents: HashMap::new(),
            shutdown_requested: false,
        };
        assert_eq!(s.batch(batch).expect("the batch runs"), None);
        client.receiver.try_iter().collect()
    }

    fn published_versions(sent: &[Message]) -> Vec<Value> {
        sent.iter()
            .filter_map(|m| match m {
                Message::Notification(n) if n.method == "textDocument/publishDiagnostics" => {
                    Some(n.params["version"].clone())
                }
                _ => None,
            })
            .collect()
    }

    /// Two edits in one batch publish once, for the last version.
    #[test]
    fn a_batch_publishes_each_changed_document_once() {
        let sent = run_batch(vec![
            open("x = (\n"),
            change(2, "x = 1\n"),
            change(3, "x = (\n"),
        ]);
        assert_eq!(published_versions(&sent), vec![json!(3)]);
    }

    /// A request answered mid-batch sees the edits before it, not after.
    #[test]
    fn a_request_sees_the_edits_before_it() {
        let sent = run_batch(vec![
            open("x = 1\n"),
            symbols_request(7),
            change(2, "y = 1\n"),
        ]);
        let Some(Message::Response(response)) =
            sent.iter().find(|m| matches!(m, Message::Response(_)))
        else {
            panic!("no response in {sent:?}");
        };
        let result = response.response_result.as_ref().expect("an ok response");
        assert_eq!(result[0]["name"], json!("x"));
    }

    /// A request cancelled in the same batch is answered `RequestCanceled`.
    #[test]
    fn a_request_cancelled_in_its_batch_is_not_computed() {
        let sent = run_batch(vec![
            open("x = 1\n"),
            symbols_request(7),
            notification("$/cancelRequest", json!({"id": 7})),
        ]);
        let Some(Message::Response(response)) =
            sent.iter().find(|m| matches!(m, Message::Response(_)))
        else {
            panic!("no response in {sent:?}");
        };
        let error = response
            .response_result
            .as_ref()
            .expect_err("an error response");
        assert_eq!(error.code, ErrorCode::RequestCanceled as i32);
    }

    /// Closing a document clears its diagnostics, and no later publish in the
    /// batch brings them back.
    #[test]
    fn closing_clears_diagnostics() {
        let sent = run_batch(vec![
            open("x = (\n"),
            notification(
                "textDocument/didClose",
                json!({"textDocument": {"uri": URI}}),
            ),
        ]);
        let publishes: Vec<&Notification> = sent
            .iter()
            .filter_map(|m| match m {
                Message::Notification(n) if n.method == "textDocument/publishDiagnostics" => {
                    Some(n)
                }
                _ => None,
            })
            .collect();
        assert_eq!(publishes.len(), 1, "{sent:?}");
        assert_eq!(publishes[0].params["diagnostics"], json!([]));
    }

    /// A malformed notification is logged and does not end the session.
    #[test]
    fn a_malformed_notification_is_logged() {
        let sent = run_batch(vec![notification(
            "textDocument/didOpen",
            json!({"nope": 1}),
        )]);
        assert!(
            sent.iter()
                .any(|m| matches!(m, Message::Notification(n) if n.method == "window/logMessage")),
            "{sent:?}"
        );
    }
}
