//! Shared buffer for uint-indexed string stream sources.
//!
//! [`UIntStreamBuffer`] captures the buffer, sliding-window indexing, and
//! per-producer obsolete-predicate bookkeeping that is common to every
//! streaming `UInt → String` data source (stdin, HTTP server, etc.).

use std::collections::HashMap;

use intervalsets::{Bounding, Interval, IntervalSet, ops::Difference};
use log::trace;
use smol_str::SmolStr;

use crate::interpreter::{ColumnValue, Value, tiling::Predicate};

/// Buffer and predicate bookkeeping for a uint-indexed string stream.
///
/// Maintains a sliding window of [`SmolStr`] values indexed by monotonically
/// increasing `usize` keys.  Released indices are drained from the front of
/// `buffer`; `start_idx` records the logical offset so that external keys
/// remain stable across drains.
pub(crate) struct UIntStreamBuffer {
    /// Buffered values.  `buffer[j]` corresponds to logical index `start_idx + j`.
    pub(crate) buffer: Vec<SmolStr>,

    /// Logical index of `buffer[0]`.  Indices below this have been released.
    pub(crate) start_idx: usize,

    /// One past the highest logical index that has been pushed.
    pub(crate) ready_size: usize,

    /// `true` once the producing thread has signalled end-of-stream.
    pub(crate) eof_reached: bool,

    /// `true` once a universal release has been received.
    closed: bool,

    /// Per-producer obsolete predicates, accumulated via union on each [`release`].
    pub(crate) obsolete_predicates: HashMap<String, Predicate>,
}

impl UIntStreamBuffer {
    pub(crate) fn new() -> Self {
        Self {
            buffer: Vec::new(),
            start_idx: 0,
            ready_size: 0,
            eof_reached: false,
            closed: false,
            obsolete_predicates: HashMap::new(),
        }
    }

    /// Append `value` to the buffer and increment `ready_size`.
    pub(crate) fn push(&mut self, value: SmolStr) {
        self.buffer.push(value);
        self.ready_size += 1;
    }

    pub(crate) fn get_opt(&self, i: usize) -> Option<&SmolStr> {
        if self.closed || self.start_idx > i || i >= self.ready_size {
            None
        } else {
            Some(&self.buffer[i - self.start_idx])
        }
    }

    pub(crate) fn get(&self, i: usize) -> &SmolStr {
        self.get_opt(i)
            .unwrap_or_else(|| panic!("Invalid UIntStreamBuffer::get({i})"))
    }

    /// Release all entries up to and including `i`, draining the buffer front.
    pub(crate) fn release_index(&mut self, i: usize) {
        if i < self.start_idx {
            return;
        }
        if i >= self.ready_size {
            panic!(
                "Invalid UIntStreamBuffer::release_index({i}), ready_size={}",
                self.ready_size
            );
        }
        self.buffer.drain(0..(i - self.start_idx + 1));
        self.start_idx = i + 1;
    }

    pub(crate) fn close(&mut self) {
        self.closed = true;
    }

    pub(crate) fn get_yield_predicate(&self) -> Predicate {
        let predicate = if self.eof_reached {
            Predicate::True
        } else if self.ready_size == 0 {
            Predicate::False
        } else {
            Predicate::LessThanEq(Value::UInt(self.ready_size - 1))
        };
        trace!("UIntStreamBuffer yielding {predicate:?}");
        predicate
    }

    /// Return the non-obsolete indices in `[start_idx, ready_size)` for `producer`.
    pub(crate) fn get_elements(&self, producer: &str) -> ColumnValue {
        let filter = self
            .obsolete_predicates
            .get(producer)
            .unwrap_or_else(|| panic!("Unknown producer: {}", producer));
        match filter {
            Predicate::Intervals(intervals) => {
                if self.start_idx >= self.ready_size {
                    return ColumnValue::from_uints(Vec::new());
                }
                // Compute [start_idx, ready_size-1] \ intervals.
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
                        _ => panic!("unexpected interval bounds in UIntStreamBuffer::get_elements"),
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
            _ => panic!("Unsupported predicate for UIntStreamBuffer::get_elements: {filter:?}"),
        }
    }

    /// Update per-producer obsolete predicates and release any buffer entries
    /// that all producers agree are no longer needed.
    pub(crate) fn release(&mut self, producer: &str, mut obsolete: Predicate) {
        let pred = self
            .obsolete_predicates
            .entry(producer.to_string())
            .or_insert(Predicate::False);
        *pred = pred.union(&obsolete);
        for pred in self.obsolete_predicates.values() {
            obsolete = obsolete.intersect(pred);
        }
        trace!("UIntStreamBuffer::release: {obsolete:?}");
        match &obsolete {
            Predicate::LessThanEq(Value::UInt(i)) => self.release_index(*i),
            Predicate::True => self.close(),
            _ => {}
        }
    }
}
