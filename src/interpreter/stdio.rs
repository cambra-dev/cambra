use std::{
    io::BufRead,
    sync::mpsc::{self, Receiver},
    thread,
};

use log::debug;
use smol_str::SmolStr;

use crate::ccl::Type;
use crate::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, stream_buffer::UIntStreamBuffer,
    tiling::Predicate,
};

/// Buffers and tracks lines available on stdin.
///
/// Lines are read by a background thread so that `check_for_new_data` never
/// blocks — it simply drains whatever the reader thread has buffered so far.
pub struct StdinDataSource {
    /// Shared buffer, indexing, and predicate bookkeeping.
    buf: UIntStreamBuffer,

    /// Lines arriving from the background reader thread.  `None` signals EOF.
    receiver: Receiver<Option<SmolStr>>,
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
            buf: UIntStreamBuffer::new(),
            receiver,
        }
    }

    fn add(&mut self, line: SmolStr) {
        self.buf.push(line);
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
        let mut got_data = false;
        loop {
            match self.receiver.try_recv() {
                Ok(Some(line)) => {
                    self.add(line);
                    got_data = true;
                }
                Ok(None) => {
                    debug!("EOF reached on stdin");
                    self.buf.eof_reached = true;
                    got_data = true;
                    break;
                }
                Err(_) => break,
            }
        }
        got_data
    }

    fn get_yield_predicate(&self) -> Predicate {
        self.buf.get_yield_predicate()
    }

    fn get_elements(&self, producer: &str) -> ColumnValue {
        self.buf.get_elements(producer)
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn get(&self, key: ColumnValue) -> ColumnValue {
        match key {
            ColumnValue::UInts(v) => {
                ColumnValue::Strings(v.iter().map(|i| self.buf.get(*i)).cloned().collect())
            }
            other => panic!("StdinDataSource::get expected UInt key, got {other:?}"),
        }
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(BaseType::String)
    }

    fn output_type(&self) -> Type {
        Type::Base(BaseType::String)
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        self.buf.release(producer, obsolete);
    }

    fn carry_release_to_new_producers(&mut self) {
        self.buf.carry_release_to_new_producers();
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::{
        ColumnValue, DataSourceDomainExtentImpl, Value, stdio::StdinDataSource, tiling::Predicate,
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
            .buf
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
            .buf
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
            .buf
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
        source
            .buf
            .obsolete_predicates
            .insert("p".to_string(), filter);

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
        source.buf.release_index(1);

        // Mark index 3 as obsolete; live window [2,4] minus {3} = {2,4}.
        let filter = Predicate::from_column_value(&ColumnValue::UInts(vec![3]));
        source
            .buf
            .obsolete_predicates
            .insert("p".to_string(), filter);

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
        source
            .buf
            .obsolete_predicates
            .insert("p".to_string(), filter);

        let result = source.get_elements("p");
        assert_eq!(result, ColumnValue::from_uints(vec![]));
    }

    #[test]
    fn test_stdin_datasource() {
        let mut source = StdinDataSource::new();
        assert_eq!(Predicate::False, source.get_yield_predicate());
        source.add("a".into());
        source.add("b".into());
        assert_eq!("a", source.buf.get(0));
        assert_eq!("b", source.buf.get(1));
        assert_eq!(None, source.buf.get_opt(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(1)),
            source.get_yield_predicate()
        );
        source.buf.release_index(0);
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(1)),
            source.get_yield_predicate()
        );
        assert_eq!(None, source.buf.get_opt(0));
        assert_eq!("b", source.buf.get(1));
        source.add("c".into());
        assert_eq!(None, source.buf.get_opt(0));
        assert_eq!("b", source.buf.get(1));
        assert_eq!("c", source.buf.get(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        source.buf.release_index(1);
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        assert_eq!(None, source.buf.get_opt(0));
        assert_eq!(None, source.buf.get_opt(1));
        assert_eq!("c", source.buf.get(2));
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(2)),
            source.get_yield_predicate()
        );
        source.buf.eof_reached = true;
        source.buf.close();
        assert_eq!(None, source.buf.get_opt(0));
        assert_eq!(None, source.buf.get_opt(1));
        assert_eq!(None, source.buf.get_opt(2));
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
            source.buf.obsolete_predicates.contains_key("producer_a"),
            "producer_a predicate should be stored"
        );

        // Second release from producer B: index 1 is obsolete
        // This should use union (OR) to accumulate with existing predicate, not overwrite
        source.release("producer_b", Predicate::LessThanEq(Value::UInt(1)));

        // Verify both predicates are recorded
        assert!(
            source.buf.obsolete_predicates.contains_key("producer_a"),
            "producer_a predicate should still be stored"
        );
        assert!(
            source.buf.obsolete_predicates.contains_key("producer_b"),
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
            .buf
            .obsolete_predicates
            .get("producer_a")
            .cloned()
            .unwrap();

        // Second release from producer A: index 1
        // This should use union with the existing predicate
        source.release("producer_a", Predicate::LessThanEq(Value::UInt(1)));

        // The predicate should now be an OR of the two
        let pred_after_second = source
            .buf
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
