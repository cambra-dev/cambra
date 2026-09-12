//! Driving a host-channel program from a terminal.
//!
//! A program that reads host channels needs a host. This is the one the binary
//! supplies: rows arrive as JSON lines on stdin and leave as JSON lines on
//! stdout, one object per line.
//!
//! ```text
//! in   {"source": "price_updates", "rows": [{"ticker": "BTC-USD", "price": 8169291000000}]}
//! out  {"sink": "btc_line", "rows": [{"qty": 2, "price": 8169291000000, "total": 16338582000000}]}
//! ```
//!
//! Development plumbing, not a deployment surface. It exists so the app and the
//! inspector can be built against `cargo run` before the WebAssembly host is
//! ready, and so a host-channel program in the gallery can be driven by a
//! subprocess test the way `streaming_echo` drives the real stdin.
//!
//! A program with declared channels does not also read `stdin()`: stdin is the
//! channel transport for the length of the run.

use std::io::{BufRead, Write};
use std::sync::mpsc::{self, Receiver};
use std::thread;

use serde::Deserialize;

use crate::ccl::channels::{Channels, row_from_json, row_to_json};

/// One line of input: rows for a named source.
#[derive(Debug, Deserialize)]
pub struct SourceLine {
    /// The source to push into.
    pub source: String,
    /// The rows, each an object matching the source's declared row type.
    pub rows: Vec<serde_json::Value>,
}

/// Rows a sink produced, ready to write.
#[derive(Debug, serde::Serialize)]
struct SinkLine<'a> {
    sink: &'a str,
    rows: Vec<serde_json::Value>,
}

/// Lines arriving from stdin, read on a background thread.
///
/// The thread is what keeps the tick loop non-blocking: the driver polls
/// [`take`](StdinLines::take) between ticks and never waits on a reader. It is
/// the same shape [`StdinDataSource`](crate::interpreter::StdinDataSource) uses,
/// and the reason neither can exist in a WebAssembly host.
pub struct StdinLines {
    lines: Receiver<Option<String>>,
    closed: bool,
}

impl StdinLines {
    /// Start reading stdin.
    pub fn new() -> Self {
        let (send, lines) = mpsc::channel();
        thread::spawn(move || {
            for line in std::io::stdin().lock().lines() {
                match line {
                    Ok(text) => {
                        if send.send(Some(text)).is_err() {
                            return;
                        }
                    }
                    Err(e) => {
                        eprintln!("cambra: reading stdin: {e}");
                        break;
                    }
                }
            }
            let _ = send.send(None);
        });
        Self {
            lines,
            closed: false,
        }
    }

    /// Every line that has arrived since the last call. Never blocks.
    pub fn take(&mut self) -> Vec<String> {
        let mut taken = Vec::new();
        loop {
            match self.lines.try_recv() {
                Ok(Some(line)) => taken.push(line),
                Ok(None) => {
                    self.closed = true;
                    break;
                }
                Err(_) => break,
            }
        }
        taken
    }

    /// Whether stdin has reached end of input.
    pub fn is_closed(&self) -> bool {
        self.closed
    }
}

impl Default for StdinLines {
    fn default() -> Self {
        Self::new()
    }
}

/// Push the rows one input line carries into the source it names.
///
/// A malformed line is reported and skipped rather than ending the run: a host
/// that sends one bad row has not necessarily stopped being a host, and a driver
/// that exits on it loses every row that follows.
pub fn push_line(channels: &Channels, line: &str) {
    let line = line.trim();
    if line.is_empty() {
        return;
    }
    let parsed: SourceLine = match serde_json::from_str(line) {
        Ok(parsed) => parsed,
        Err(e) => {
            eprintln!("cambra: skipping input line: {e}");
            return;
        }
    };
    let Some(source) = channels.source(&parsed.source) else {
        eprintln!(
            "cambra: skipping input line: no source named '{}'",
            parsed.source
        );
        return;
    };
    let row_type = source.borrow().row_type().clone();
    let mut rows = Vec::with_capacity(parsed.rows.len());
    for row in &parsed.rows {
        match row_from_json(row, &row_type) {
            Ok(value) => rows.push(value),
            Err(e) => {
                eprintln!("cambra: skipping a row for '{}': {e}", parsed.source);
            }
        }
    }
    source.borrow_mut().push(rows);
}

/// Write one line per sink that produced rows this tick, and report whether any
/// did.
///
/// Flushed per line so a reader downstream of a pipe sees a row when the program
/// produced it rather than when the buffer filled.
pub fn write_sink_rows(channels: &Channels, out: &mut impl Write) -> std::io::Result<bool> {
    let mut wrote = false;
    let mut names: Vec<&str> = channels.sinks().map(|(name, _)| name).collect();
    names.sort_unstable();
    for name in names {
        let drained = channels.drain_sink(name);
        if drained.is_empty() {
            continue;
        }
        let mut rows = Vec::with_capacity(drained.len());
        for row in &drained {
            match row_to_json(row) {
                Ok(json) => rows.push(json),
                Err(e) => eprintln!("cambra: dropping a row from '{name}': {e}"),
            }
        }
        if rows.is_empty() {
            continue;
        }
        let line =
            serde_json::to_string(&SinkLine { sink: name, rows }).expect("a sink line serializes");
        writeln!(out, "{line}")?;
        out.flush()?;
        wrote = true;
    }
    Ok(wrote)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::channels::ChannelDecl;
    use crate::ccl::context::GlobalContext;
    use crate::interpreter::{ColumnValue, DataSink, Tile};
    use test_log::test;

    fn channels_with_a_price_source() -> Channels {
        let mut ctx = GlobalContext::default();
        ctx.register_channels(&[ChannelDecl::source(
            "price_updates",
            "{ticker: String, price: Int}",
        )])
        .expect("the declarations are well formed")
    }

    #[test]
    fn a_line_pushes_its_rows_into_the_named_source() {
        let channels = channels_with_a_price_source();
        push_line(
            &channels,
            r#"{"source": "price_updates", "rows": [{"ticker": "BTC-USD", "price": 7}]}"#,
        );
        let source = channels.source("price_updates").expect("a declared source");
        assert_eq!(source.borrow().rows_held(), 1);
    }

    /// One bad line does not end the run, because the host is still a host.
    #[test]
    fn a_malformed_line_is_skipped() {
        let channels = channels_with_a_price_source();
        push_line(&channels, "not json");
        push_line(&channels, r#"{"source": "nowhere", "rows": []}"#);
        push_line(
            &channels,
            r#"{"source": "price_updates", "rows": [{"ticker": "BTC-USD"}]}"#,
        );
        push_line(
            &channels,
            r#"{"source": "price_updates", "rows": [{"ticker": "BTC-USD", "price": 7}]}"#,
        );
        let source = channels.source("price_updates").expect("a declared source");
        assert_eq!(
            source.borrow().rows_held(),
            1,
            "the well-formed row still arrives"
        );
    }

    #[test]
    fn a_blank_line_is_not_an_error() {
        let channels = channels_with_a_price_source();
        push_line(&channels, "   ");
        assert_eq!(
            channels
                .source("price_updates")
                .expect("a declared source")
                .borrow()
                .rows_held(),
            0
        );
    }

    #[test]
    fn a_sink_writes_one_line_per_tick_that_produced_rows() {
        let mut ctx = GlobalContext::default();
        let channels = ctx
            .register_channels(&[ChannelDecl::sink("btc_line", "{qty: Int}")])
            .expect("the declarations are well formed");
        let sink = channels.sink("btc_line").expect("a declared sink");

        let mut out = Vec::new();
        assert!(
            !write_sink_rows(&channels, &mut out).expect("writing to a vec"),
            "a tick that produced nothing reports nothing"
        );
        assert!(
            out.is_empty(),
            "a tick that produced nothing writes nothing"
        );

        sink.process(&Tile::Scalar(ColumnValue::Records(
            [("qty".to_string(), ColumnValue::Ints(vec![2]))]
                .into_iter()
                .collect(),
        )));
        assert!(write_sink_rows(&channels, &mut out).expect("writing to a vec"));
        assert_eq!(
            String::from_utf8(out).expect("utf-8"),
            "{\"sink\":\"btc_line\",\"rows\":[{\"qty\":2}]}\n"
        );
    }
}
