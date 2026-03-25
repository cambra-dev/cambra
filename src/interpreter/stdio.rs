use std::{
    io::BufRead,
    sync::mpsc::{self, Receiver, TryRecvError},
    thread,
};

use log::{debug, trace};

use crate::interpreter::{
    tiling::Predicate, ColumnValue, DataSourceDomainExtentImpl, Extent, Value,
};

/// Buffers and tracks lines available on stdin.
///
/// Lines are read by a background thread so that `check_for_new_data` never
/// blocks — it simply drains whatever the reader thread has buffered so far.
pub struct StdinDataSource {
    /// Currently available data.
    buffer: Vec<String>,

    /// Offset of indices in the buffer.  Indices less than this have been released.
    start_idx: usize,

    /// Logical size of the buffer, including released lines.
    ready_size: usize,

    /// Whether EOF has been observed on stdin.
    eof_reached: bool,

    /// Whether the source has been released with Universal.
    closed: bool,

    /// Lines arriving from the background reader thread.  `None` signals EOF.
    receiver: Receiver<Option<String>>,
}

impl StdinDataSource {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let mut reader = std::io::BufReader::new(std::io::stdin());
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) => {
                        // EOF — signal the main thread and stop.
                        let _ = sender.send(None);
                        return;
                    }
                    Ok(_) => {
                        if line.ends_with('\n') {
                            line.pop();
                            if line.ends_with('\r') {
                                line.pop();
                            }
                        }
                        if sender.send(Some(line)).is_err() {
                            // Receiver was dropped (source closed); stop reading.
                            return;
                        }
                    }
                    Err(err) => panic!("Error reading from stdin: {err}"),
                }
            }
        });
        Self {
            buffer: Vec::new(),
            start_idx: 0,
            ready_size: 0,
            eof_reached: false,
            closed: false,
            receiver,
        }
    }

    fn get_opt(&self, i: usize) -> Option<&str> {
        if self.closed || self.start_idx > i || i >= self.ready_size {
            None
        } else {
            Some(&self.buffer[i - self.start_idx])
        }
    }

    /// Returns the line at the given index.
    fn get(&self, i: usize) -> &str {
        self.get_opt(i)
            .unwrap_or_else(|| panic!("Invalid StdinDataSource::get({i})"))
    }

    fn add(&mut self, line: String) {
        self.buffer.push(line);
        self.ready_size += 1;
    }

    /// Releases all lines up to and including the given index.
    fn release_index(&mut self, i: usize) {
        if i < self.start_idx {
            // Already released, do nothing
            return;
        }
        if i >= self.ready_size {
            panic!(
                "Invalid StdinDataSource::release, {} vs {}, {}",
                i, self.ready_size, self.start_idx
            );
        }
        self.buffer.drain(0..(i - self.start_idx + 1));
        self.start_idx = i + 1;
    }

    fn close(&mut self) {
        self.closed = true;
    }
}

impl Default for StdinDataSource {
    fn default() -> Self {
        Self::new()
    }
}

impl DataSourceDomainExtentImpl for StdinDataSource {
    fn get_id(&self) -> &str {
        "stdin"
    }

    /// Drains any lines that the background reader thread has buffered.
    ///
    /// Returns `true` if at least one new line (or EOF) was received, which
    /// tells the scheduler to re-notify consumers.  Never blocks.
    fn check_for_new_data(&mut self) -> bool {
        trace!("Checking for new data on stdin");
        let mut got_data = false;
        loop {
            match self.receiver.try_recv() {
                Ok(Some(line)) => {
                    self.add(line);
                    got_data = true;
                }
                Ok(None) => {
                    debug!("EOF reached on stdin");
                    self.eof_reached = true;
                    got_data = true;
                    break;
                }
                Err(TryRecvError::Empty) => break,
                Err(TryRecvError::Disconnected) => break,
            }
        }
        got_data
    }

    fn get_yield_predicate(&self) -> Predicate {
        let predicate = if self.eof_reached {
            Predicate::True
        } else if self.ready_size == 0 {
            Predicate::False
        } else {
            Predicate::LessThanEq(Value::UInt(self.ready_size - 1))
        };
        debug!("StdinDataSource yielding {predicate:?}");
        predicate
    }

    /// Returns the currently readable set of indices.
    fn get_elements(&self) -> ColumnValue {
        ColumnValue::UInts((self.start_idx..self.ready_size).collect())
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(crate::interpreter::BaseType::UInt)
    }

    fn get(&self, key: &Value) -> Value {
        match key {
            Value::UInt(i) => Value::String(self.get(*i).to_string()),
            other => panic!("StdinDataSource::get expected UInt key, got {other:?}"),
        }
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(crate::interpreter::BaseType::String)
    }

    fn release(&mut self, obsolete: Predicate) {
        debug!("StdinDataSource::release: {obsolete:?}");
        match &obsolete {
            Predicate::LessThanEq(Value::UInt(i)) => self.release_index(*i),
            Predicate::True => self.close(),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::{
        stdio::StdinDataSource, tiling::Predicate, DataSourceDomainExtentImpl, Value,
    };
    use test_log::test;

    #[test]
    fn test_stdin_datasource() {
        let mut source = StdinDataSource::new();
        assert_eq!(Predicate::False, source.get_yield_predicate());
        source.add("a".to_string());
        source.add("b".to_string());
        assert_eq!("a", source.get(0));
        assert_eq!("b", source.get(1));
        assert_eq!(None, source.get_opt(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(1)),
            source.get_yield_predicate()
        );
        source.release_index(0);
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(1)),
            source.get_yield_predicate()
        );
        assert_eq!(None, source.get_opt(0));
        assert_eq!("b", source.get(1));
        source.add("c".to_string());
        assert_eq!(None, source.get_opt(0));
        assert_eq!("b", source.get(1));
        assert_eq!("c", source.get(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        source.release_index(1);
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        assert_eq!(None, source.get_opt(0));
        assert_eq!(None, source.get_opt(1));
        assert_eq!("c", source.get(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        source.eof_reached = true;
        source.close();
        assert_eq!(None, source.get_opt(0));
        assert_eq!(None, source.get_opt(1));
        assert_eq!(None, source.get_opt(2));
        assert_eq!(Predicate::True, source.get_yield_predicate());
    }
}
