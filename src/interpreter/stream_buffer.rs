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
        if obsolete.is_true() {
            self.close();
            return;
        }
        if let Some(i) = self.released_prefix(&obsolete) {
            self.release_index(i);
        }
    }

    /// The highest index such that every index up to it is obsolete for every
    /// producer, or `None` when the buffer's first live index is still wanted.
    ///
    /// Buffered values are dropped by prefix, so a release only frees memory to
    /// the extent it covers an unbroken run from [`start_idx`](Self::start_idx).
    /// The predicate is asked index by index rather than matched on its shape:
    /// the intersection of several producers' released sets arrives as
    /// [`Predicate::Intervals`] once any producer has released a non-prefix
    /// region, and matching only the [`Predicate::LessThanEq`] shape silently
    /// declines to free anything in that case.
    ///
    /// The scan is amortized `O(1)` per release: it starts at `start_idx` and
    /// stops at the first index still wanted, and `start_idx` only ever
    /// advances, so no index is examined after the release that frees it.
    fn released_prefix(&self, obsolete: &Predicate) -> Option<usize> {
        let mut last = None;
        for i in self.start_idx..self.ready_size {
            if !obsolete.contains(&Value::UInt(i)) {
                break;
            }
            last = Some(i);
        }
        last
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use intervalsets::Interval;

    fn buffer_with(n: usize) -> UIntStreamBuffer {
        let mut buf = UIntStreamBuffer::new();
        for i in 0..n {
            buf.push(SmolStr::new(format!("e{i}")));
        }
        buf
    }

    /// An interval covering `[0, i]`, the shape a producer's accumulated
    /// released set takes once it has consumed a prefix.
    fn through(i: usize) -> Predicate {
        Predicate::Intervals(IntervalSet::from(Interval::closed(
            Value::UInt(0),
            Value::UInt(i),
        )))
    }

    /// A single producer releasing a prefix frees it, whichever predicate shape
    /// carries the release.
    ///
    /// The regression this pins: `release` used to advance the buffer only for a
    /// `LessThanEq` predicate, and the intersection it computes is an
    /// `Intervals`, so nothing was ever freed and the buffer grew for the life
    /// of the program.
    #[test]
    fn releasing_a_prefix_frees_it() {
        let mut buf = buffer_with(8);
        buf.release("p", through(4));
        assert_eq!(
            buf.start_idx, 5,
            "indices 0..=4 are obsolete for every producer"
        );
        assert_eq!(buf.buffer.len(), 3, "only 5, 6 and 7 are still wanted");
    }

    /// Memory is bounded across a long run, not just on the first release.
    #[test]
    fn a_long_run_does_not_accumulate() {
        let mut buf = UIntStreamBuffer::new();
        for i in 0..200 {
            buf.push(SmolStr::new(format!("e{i}")));
            buf.release("p", through(i));
        }
        assert_eq!(buf.start_idx, 200);
        assert!(buf.buffer.is_empty(), "held {} values", buf.buffer.len());
    }

    /// A prefix is freed only once every producer is done with it: the release
    /// is the intersection across producers, not the latest one to arrive.
    ///
    /// Both producers register before any release, which is what subscribing
    /// does (`IterateExtent::subscribe` releases `Predicate::False` to enrol
    /// with each source in its extent). A producer with no entry is not in the
    /// intersection and so does not hold anything back.
    #[test]
    fn a_prefix_is_freed_only_when_every_producer_has_released_it() {
        let mut buf = buffer_with(8);
        buf.release("fast", Predicate::False);
        buf.release("slow", Predicate::False);

        buf.release("fast", through(5));
        assert_eq!(buf.start_idx, 0, "`slow` has released nothing");

        buf.release("slow", through(2));
        assert_eq!(buf.start_idx, 3, "`slow` still wants 3 onward");

        buf.release("slow", through(5));
        assert_eq!(buf.start_idx, 6);
    }

    /// A release that does not reach the first live index frees nothing, even
    /// though it covers later ones.
    #[test]
    fn a_gap_at_the_front_holds_the_buffer() {
        let mut buf = buffer_with(8);
        let later_only = Predicate::Intervals(IntervalSet::from(Interval::closed(
            Value::UInt(3),
            Value::UInt(6),
        )));
        buf.release("p", later_only);
        assert_eq!(buf.start_idx, 0, "index 0 is still wanted");
        assert_eq!(buf.buffer.len(), 8);
    }
}
