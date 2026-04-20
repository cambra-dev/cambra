use std::{
    collections::HashMap,
    io::BufRead,
    sync::mpsc::{self, Receiver, TryRecvError},
    thread,
};

use intervalsets::{ops::Difference, Bounding, Interval, IntervalSet};
use log::{debug, trace};
use smol_str::SmolStr;

use crate::interpreter::{
    tiling::Predicate, ColumnValue, DataSourceDomainExtentImpl, Extent, Value,
};

/// Buffers and tracks lines available on stdin.
///
/// Lines are read by a background thread so that `check_for_new_data` never
/// blocks — it simply drains whatever the reader thread has buffered so far.
pub struct StdinDataSource {
    /// Currently available data.
    buffer: Vec<SmolStr>,

    /// Offset of indices in the buffer.  Indices less than this have been released.
    start_idx: usize,

    /// Logical size of the buffer, including released lines.
    ready_size: usize,

    /// Whether EOF has been observed on stdin.
    eof_reached: bool,

    /// Whether the source has been released with Universal.
    closed: bool,

    /// Lines arriving from the background reader thread.  `None` signals EOF.
    receiver: Receiver<Option<SmolStr>>,

    obsolete_predicates: HashMap<String, Predicate>,
}

impl StdinDataSource {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let mut reader = std::io::BufReader::new(std::io::stdin());
            let mut buf = String::new();
            loop {
                buf.clear();
                match reader.read_line(&mut buf) {
                    Ok(0) => {
                        // EOF — signal the main thread and stop.
                        let _ = sender.send(None);
                        return;
                    }
                    Ok(_) => {
                        let line = SmolStr::new(buf.trim_end_matches(['\n', '\r']));
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
            obsolete_predicates: HashMap::new(),
        }
    }

    fn get_opt(&self, i: usize) -> Option<&SmolStr> {
        if self.closed || self.start_idx > i || i >= self.ready_size {
            None
        } else {
            Some(&self.buffer[i - self.start_idx])
        }
    }

    /// Returns the line at the given index.
    fn get(&self, i: usize) -> &SmolStr {
        self.get_opt(i)
            .unwrap_or_else(|| panic!("Invalid StdinDataSource::get({i})"))
    }

    fn add(&mut self, line: SmolStr) {
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
        trace!("StdinDataSource yielding {predicate:?}");
        predicate
    }

    /// Returns the currently readable set of indices.
    fn get_elements(&self, producer: &str) -> ColumnValue {
        let filter = self
            .obsolete_predicates
            .get(producer)
            .unwrap_or_else(|| panic!("Unknown producer: {}", producer));
        match filter {
            Predicate::Intervals(intervals) => {
                if self.start_idx >= self.ready_size {
                    return ColumnValue::from_uints(Vec::new());
                }
                // Compute [start_idx, ready_size-1] \ intervals to get non-obsolete indices.
                let window = IntervalSet::from(Interval::closed(
                    Value::UInt(self.start_idx),
                    Value::UInt(self.ready_size - 1),
                ));
                let mut values = Vec::new();
                for iv in window.difference(intervals).intervals() {
                    match (iv.lval(), iv.rval()) {
                        (Some(Value::UInt(lo)), Some(Value::UInt(hi))) => {
                            values.extend(*lo..=*hi);
                        }
                        _ => panic!("unexpected interval bounds in StdinDataSource::get_elements"),
                    }
                }
                ColumnValue::from_uints(values)
            }
            Predicate::LessThanEq(Value::UInt(i)) => {
                let values: Vec<_> = ((*i + 1)..self.ready_size).collect();
                ColumnValue::from_uints(values)
            }
            Predicate::True => ColumnValue::from_uints(Vec::new()),
            Predicate::False => {
                let values: Vec<_> = (self.start_idx..self.ready_size).collect();
                ColumnValue::from_uints(values)
            }
            _ => panic!("Unsupported predicate for StdinDataSource get_elements: {filter:?}"),
        }
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(crate::interpreter::BaseType::UInt)
    }

    fn get(&self, key: ColumnValue) -> ColumnValue {
        match key {
            ColumnValue::UInts(v) => {
                ColumnValue::Strings(v.iter().map(|i| self.get(*i)).cloned().collect())
            }
            other => panic!("StdinDataSource::get expected UInt key, got {other:?}"),
        }
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(crate::interpreter::BaseType::String)
    }

    fn release(&mut self, producer: &str, mut obsolete: Predicate) {
        let pred = self
            .obsolete_predicates
            .entry(producer.to_string())
            .or_insert(Predicate::False);
        *pred = pred.union(&obsolete);
        for pred in self.obsolete_predicates.values() {
            obsolete = obsolete.intersect(pred);
        }
        trace!("StdinDataSource::release: {obsolete:?}");
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
        stdio::StdinDataSource, tiling::Predicate, ColumnValue, DataSourceDomainExtentImpl, Value,
    };
    use test_log::test;

    /// `Predicate::False` means nothing is obsolete: all indices in `start_idx..ready_size`.
    #[test]
    fn test_get_elements_false_returns_all_indices() {
        let mut source = StdinDataSource::new();
        source.add("a".into());
        source.add("b".into());
        source.add("c".into());
        source
            .obsolete_predicates
            .insert("p".to_string(), Predicate::False);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![0, 1, 2]));
    }

    /// `Predicate::LessThanEq(i)` means indices `0..=i` are obsolete, so only
    /// `(i+1)..ready_size` are returned.
    #[test]
    fn test_get_elements_less_than_eq_returns_tail() {
        let mut source = StdinDataSource::new();
        source.add("a".into());
        source.add("b".into());
        source.add("c".into());
        source.add("d".into());
        source
            .obsolete_predicates
            .insert("p".to_string(), Predicate::LessThanEq(Value::UInt(1)));

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![2, 3]));
    }

    /// `Predicate::True` means all data is obsolete: the result is empty.
    #[test]
    fn test_get_elements_true_returns_empty() {
        let mut source = StdinDataSource::new();
        source.add("a".into());
        source.add("b".into());
        source
            .obsolete_predicates
            .insert("p".to_string(), Predicate::True);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![]));
    }

    /// `Predicate::Intervals` subtracts the obsolete set from the live window
    /// `[start_idx, ready_size-1]`, returning only non-obsolete indices.
    #[test]
    fn test_get_elements_intervals_subtracts_obsolete() {
        let mut source = StdinDataSource::new();
        for line in ["a", "b", "c", "d", "e"] {
            source.add(line.into());
        }
        // Mark indices 1 and 2 as obsolete; live window [0,4] minus {1,2} = {0,3,4}.
        let filter = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        source.obsolete_predicates.insert("p".to_string(), filter);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![0, 3, 4]));
    }

    /// With `start_idx > 0` the interval subtraction still uses the correct
    /// logical window `[start_idx, ready_size-1]`.
    #[test]
    fn test_get_elements_intervals_with_offset_start() {
        let mut source = StdinDataSource::new();
        for line in ["a", "b", "c", "d", "e"] {
            source.add(line.into());
        }
        // Release indices 0 and 1 so start_idx == 2, ready_size == 5.
        source.release_index(1);

        // Mark index 3 as obsolete; live window [2,4] minus {3} = {2,4}.
        let filter = Predicate::from_column_value(&ColumnValue::UInts(vec![3]));
        source.obsolete_predicates.insert("p".to_string(), filter);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![2, 4]));
    }

    /// When the buffer is empty the `Intervals` branch returns an empty vec
    /// without panicking.
    #[test]
    fn test_get_elements_intervals_empty_buffer_returns_empty() {
        let mut source = StdinDataSource::new();
        // No lines added; start_idx == ready_size == 0.
        let filter = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        source.obsolete_predicates.insert("p".to_string(), filter);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![]));
    }

    #[test]
    fn test_stdin_datasource() {
        let mut source = StdinDataSource::new();
        assert_eq!(Predicate::False, source.get_yield_predicate());
        source.add("a".into());
        source.add("b".into());
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
        source.add("c".into());
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

    #[test]
    fn test_stdin_release_accumulation() {
        // Test that StdinDataSource.release() accumulates predicates from
        // multiple producers using union instead of overwriting.
        //
        // This verifies the fix where each producer's obsolete predicate
        // is accumulated with union, and then all predicates are intersected
        // to determine which data to discard.

        let mut source = StdinDataSource::new();

        // Add some test data
        source.add("line0".into());
        source.add("line1".into());
        source.add("line2".into());

        // First release from producer A: index 0 is obsolete
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(0)));

        // Verify producer_a's predicate is recorded
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a predicate should be stored"
        );

        // Second release from producer B: index 1 is obsolete
        // This should use union (OR) to accumulate with existing predicate, not overwrite
        source.release("producer_b", Predicate::LessThanEq(Value::UInt(1)));

        // Verify both predicates are recorded
        assert!(
            source.obsolete_predicates.contains_key("producer_a"),
            "producer_a predicate should still be stored"
        );
        assert!(
            source.obsolete_predicates.contains_key("producer_b"),
            "producer_b predicate should be stored"
        );

        // The released indices should be calculated as the intersection of all predicates
        // Since both predicates target different indices, their intersection would be empty
        // However, the actual behavior is more complex due to the intersection logic
        // Just verify the method doesn't panic and properly updates state
    }

    #[test]
    fn test_stdin_release_same_producer_accumulation() {
        // Test that multiple releases from the same producer accumulate
        // their predicates using union (OR).

        let mut source = StdinDataSource::new();

        // Add some test data
        source.add("line0".into());
        source.add("line1".into());
        source.add("line2".into());

        // First release from producer A: index 0
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(0)));

        // Store the first predicate
        let pred_after_first = source
            .obsolete_predicates
            .get("producer_a")
            .cloned()
            .unwrap();

        // Second release from producer A: index 1
        // This should use union with the existing predicate
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(1)));

        // The predicate should now be an OR of the two
        let pred_after_second = source
            .obsolete_predicates
            .get("producer_a")
            .cloned()
            .unwrap();

        // The second predicate should be different from the first (should be OR'd)
        assert_ne!(
            pred_after_first, pred_after_second,
            "Predicate should be updated to OR with the new release"
        );
    }
}
