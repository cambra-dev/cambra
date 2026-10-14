//! A language server for CHL, run as `cambra --lsp`. The server's behavior is
//! specified in `cambra-lsp/design-cambra-lsp.md`.

mod diagnostics;
mod document;
mod folding;
mod server;
mod symbols;

pub use server::{Ended, run};

/// An error that ends the session early: a broken connection, or a client
/// the server cannot serve.
pub type Error = Box<dyn std::error::Error + Send + Sync>;

/// Serves one client over standard input and output until it exits.
pub fn run_stdio() -> Result<Ended, Error> {
    let (connection, io_threads) = lsp_server::Connection::stdio();
    let ended = run(&connection)?;
    drop(connection);
    io_threads.join()?;
    Ok(ended)
}
