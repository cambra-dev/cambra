//! Shared buffer for uint-indexed string stream sources.
//!
//! [`UIntStreamBuffer`] captures the buffer, sliding-window indexing, and
//! per-producer obsolete-predicate bookkeeping that is common to every
//! streaming `UInt → String` data source (stdin, HTTP server, etc.).

use std::collections::HashMap;

use intervalsets::{
    Bounding, Interval, IntervalSet,
    ops::{Difference, Intersection},
};
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

    /// Where a producer registering from now on begins: it is recorded as having
    /// already released everything below this index.
    ///
    /// `0` until [`advance_new_producer_frontier`](Self::advance_new_producer_frontier)
    /// moves it, so a program's own producers — which all register before it starts
    /// consuming — read the whole buffer, including anything that arrived while
    /// the program was compiling.
    ///
    /// Replacing a running program moves it to the current position. Operators
    /// the replacement rebuilds register as new producers, and a source hands a
    /// newly-registered producer everything it still holds, so without this the
    /// replacement would recompute the program's history rather than continue it
    /// — over however much the source happened to retain, and re-emitting an
    /// output for every input the replaced version had already answered.
    new_producer_frontier: usize,
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
            new_producer_frontier: 0,
        }
    }

    /// Append `value` to the buffer and increment `ready_size`.
    pub(crate) fn push(&mut self, value: SmolStr) {
        if self.closed {
            // A closed buffer's universal release covers this index too, so
            // holding the value would re-accumulate what `close` just freed.
            self.start_idx += 1;
        } else {
            self.buffer.push(value);
        }
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

    /// Record that no producer will read any index again, and free what is held.
    pub(crate) fn close(&mut self) {
        self.closed = true;
        self.buffer.clear();
        self.start_idx = self.ready_size;
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

    /// The buffered indices, `[start_idx, ready_size)`.
    fn live_window(&self) -> IntervalSet<Value> {
        if self.start_idx >= self.ready_size {
            IntervalSet::empty()
        } else {
            IntervalSet::from(Interval::closed(
                Value::UInt(self.start_idx),
                Value::UInt(self.ready_size - 1),
            ))
        }
    }

    /// The indices `guard` admits, and the only place the buffer reads a guard's
    /// shape.
    ///
    /// Four predicate shapes inhabit a `UInt` extent, and each denotes an index
    /// set directly. A guard of any other shape was built for a different
    /// extent: the buffer can neither subtract it in [`get_elements`] nor free a
    /// prefix for it, so it fails here rather than being recorded as obsolete
    /// and then admitting every index for the life of the program.
    ///
    /// [`get_elements`]: Self::get_elements
    fn index_set(guard: &Predicate) -> IntervalSet<Value> {
        match guard {
            Predicate::True => IntervalSet::from(Interval::unbounded()),
            Predicate::False => IntervalSet::empty(),
            Predicate::LessThanEq(v @ Value::UInt(_)) => {
                IntervalSet::from(Interval::unbound_closed(v.clone()))
            }
            Predicate::Intervals(s) if s.intervals().iter().all(Self::is_index_interval) => {
                s.clone()
            }
            _ => {
                panic!("UIntStreamBuffer guard is not a subset of its UInt index extent: {guard:?}")
            }
        }
    }

    /// `true` when each of `interval`'s bounds is an index or absent.
    fn is_index_interval(interval: &Interval<Value>) -> bool {
        [interval.lval(), interval.rval()]
            .into_iter()
            .all(|b| matches!(b, None | Some(Value::UInt(_))))
    }

    /// Return the non-obsolete indices in `[start_idx, ready_size)` for `producer`.
    pub(crate) fn get_elements(&self, producer: &str) -> ColumnValue {
        let obsolete = self
            .obsolete_predicates
            .get(producer)
            .unwrap_or_else(|| panic!("Unknown producer: {producer}"));
        let live = self.live_window().difference(&Self::index_set(obsolete));
        let mut indices = Vec::new();
        for iv in live.intervals() {
            match (iv.lval(), iv.rval()) {
                (Some(Value::UInt(lo)), Some(Value::UInt(hi))) => indices.extend(*lo..=*hi),
                _ => unreachable!(
                    "subtracting from the live window leaves every interval closed on both sides"
                ),
            }
        }
        ColumnValue::from_uints(indices)
    }

    /// Start any producer that registers from now on at the current position, so
    /// that a program replacing this one continues the stream rather than
    /// reprocessing it. See
    /// [`new_producer_frontier`](Self::new_producer_frontier).
    pub(crate) fn advance_new_producer_frontier(&mut self) {
        self.new_producer_frontier = self.ready_size;
    }

    /// Where a producer registering now begins.
    pub(crate) fn frontier(&self) -> usize {
        self.new_producer_frontier
    }

    /// What a producer registering now counts as having already released.
    fn new_producer_obsolete(&self) -> Predicate {
        match self.new_producer_frontier {
            0 => Predicate::False,
            n => Predicate::LessThanEq(Value::UInt(n - 1)),
        }
    }

    /// Update per-producer obsolete predicates and release any buffer entries
    /// that all producers agree are no longer needed.
    pub(crate) fn release(&mut self, producer: &str, obsolete: Predicate) {
        let starts_at = self.new_producer_obsolete();
        let recorded = self
            .obsolete_predicates
            .entry(producer.to_string())
            .or_insert(starts_at);
        *recorded = recorded.union(&obsolete);

        // Every registered producer is done with every index, so nothing will be
        // read again. A producer with no entry has not subscribed, and so holds
        // nothing back.
        if self.obsolete_predicates.values().all(Predicate::is_true) {
            self.close();
            return;
        }

        // Each producer's accumulated set is every index it will not read again,
        // so their intersection is what the buffer may drop. The intersection is
        // over those accumulated sets rather than over this release and them:
        // a producer's earlier releases still stand. Every recorded guard passes
        // through `index_set` here, which is where one built for another extent
        // fails.
        let agreed = self
            .obsolete_predicates
            .values()
            .fold(IntervalSet::from(Interval::unbounded()), |agreed, pred| {
                agreed.intersection(&Self::index_set(pred))
            });
        trace!("UIntStreamBuffer::release: {agreed:?}");
        if let Some(i) = self.released_prefix(&agreed) {
            self.release_index(i);
        }
    }

    /// The highest buffered index that `agreed` covers in an unbroken run from
    /// [`start_idx`](Self::start_idx), or `None` when the first buffered index is
    /// still wanted.
    ///
    /// Values are dropped from the front, so a release frees memory only over
    /// such a run. A covered region with a live index in front of it is still
    /// recorded per producer, and [`get_elements`](Self::get_elements) still
    /// withholds it; only the bytes are held until the front is released.
    fn released_prefix(&self, agreed: &IntervalSet<Value>) -> Option<usize> {
        // Intervals in a set over a discrete domain are sorted and non-adjacent,
        // so the run starting at `start_idx` is the whole of the first interval.
        let released = self.live_window().intersection(agreed);
        match released
            .intervals()
            .first()
            .map(|iv| (iv.lval(), iv.rval()))
        {
            Some((Some(Value::UInt(lo)), Some(Value::UInt(hi)))) if *lo == self.start_idx => {
                Some(*hi)
            }
            Some((Some(Value::UInt(_)), Some(Value::UInt(_)))) | None => None,
            Some(_) => unreachable!(
                "intersecting with the live window leaves every interval closed on both sides"
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn buffer_with(n: usize) -> UIntStreamBuffer {
        let mut buf = UIntStreamBuffer::new();
        for i in 0..n {
            buf.push(SmolStr::new(format!("e{i}")));
        }
        buf
    }

    /// The indices `lo..=hi`, the shape a producer's accumulated released set
    /// takes once it has consumed a contiguous run.
    fn covering(lo: usize, hi: usize) -> Predicate {
        Predicate::Intervals(IntervalSet::from(Interval::closed(
            Value::UInt(lo),
            Value::UInt(hi),
        )))
    }

    /// A single producer releasing a prefix frees it, whichever of the index
    /// extent's predicate shapes carries the release.
    #[test]
    fn releasing_a_prefix_frees_it() {
        for release in [covering(0, 4), Predicate::LessThanEq(Value::UInt(4))] {
            let mut buf = buffer_with(8);
            buf.release("p", release);
            assert_eq!(
                buf.start_idx, 5,
                "indices 0..=4 are obsolete for every producer"
            );
            assert_eq!(buf.buffer.len(), 3, "only 5, 6 and 7 are still wanted");
        }
    }

    /// Memory is bounded across a long run, not just on the first release.
    #[test]
    fn a_long_run_does_not_accumulate() {
        let mut buf = UIntStreamBuffer::new();
        for i in 0..200 {
            buf.push(SmolStr::new(format!("e{i}")));
            buf.release("p", covering(0, i));
        }
        assert_eq!(buf.start_idx, 200);
        assert!(buf.buffer.is_empty(), "held {} values", buf.buffer.len());
    }

    /// A prefix is freed only once every producer is done with it: the release
    /// is the intersection across producers, not the latest one to arrive.
    ///
    /// Both producers register before any release, which is what subscribing
    /// does (`IterateExtent::subscribe` releases `Predicate::False` to register
    /// with each source in its extent). A producer with no entry is not in the
    /// intersection and so does not hold anything back.
    #[test]
    fn a_prefix_is_freed_only_when_every_producer_has_released_it() {
        let mut buf = buffer_with(8);
        buf.release("fast", Predicate::False);
        buf.release("slow", Predicate::False);

        buf.release("fast", covering(0, 5));
        assert_eq!(buf.start_idx, 0, "`slow` has released nothing");

        buf.release("slow", covering(0, 2));
        assert_eq!(buf.start_idx, 3, "`slow` still wants 3 onward");

        buf.release("slow", covering(0, 5));
        assert_eq!(buf.start_idx, 6);
    }

    /// A release that does not reach the first live index frees nothing, even
    /// though it covers later ones, and `get_elements` still withholds the
    /// indices it covers.
    #[test]
    fn a_gap_at_the_front_holds_the_buffer() {
        let mut buf = buffer_with(8);
        buf.release("p", covering(3, 6));
        assert_eq!(buf.start_idx, 0, "index 0 is still wanted");
        assert_eq!(buf.buffer.len(), 8);
        assert_eq!(
            buf.get_elements("p"),
            ColumnValue::from_uints(vec![0, 1, 2, 7])
        );
    }

    /// Two releases that meet form one run: adjacent intervals over a discrete
    /// domain merge, so the prefix is the first interval of the accumulated set
    /// and no per-index probe is needed to find its end.
    #[test]
    fn releases_that_meet_free_the_whole_run() {
        let mut buf = buffer_with(8);
        buf.release("p", covering(3, 5));
        assert_eq!(buf.start_idx, 0);
        buf.release("p", covering(0, 2));
        assert_eq!(buf.start_idx, 6, "0..=2 and 3..=5 are one run");
    }

    /// A release reaching past the buffered indices frees what is buffered.
    #[test]
    fn a_release_past_the_end_frees_what_is_held() {
        let mut buf = buffer_with(3);
        buf.release("p", covering(0, 99));
        assert_eq!(buf.start_idx, 3);
        assert!(buf.buffer.is_empty());
    }

    /// A universal release frees the buffer rather than only marking the source
    /// closed, and a value pushed afterwards is not retained either.
    #[test]
    fn closing_frees_the_buffer() {
        let mut buf = buffer_with(8);
        buf.release("p", Predicate::True);
        assert!(buf.buffer.is_empty());
        assert_eq!(buf.start_idx, 8);

        buf.push(SmolStr::new("e8"));
        assert!(buf.buffer.is_empty(), "the release covers index 8 too");
        assert_eq!(buf.ready_size, 9);
        assert_eq!(buf.get_opt(8), None);
    }

    /// A guard built for another extent fails at the buffer's boundary. Accepted
    /// silently it would be recorded as obsolete, admit no index, and hold every
    /// value for the life of the program.
    #[test]
    #[should_panic(expected = "not a subset of its UInt index extent")]
    fn a_guard_from_another_extent_is_rejected() {
        let mut buf = buffer_with(8);
        buf.release(
            "p",
            Predicate::Record(HashMap::from([(
                "k".to_string(),
                Predicate::LessThanEq(Value::UInt(4)),
            )])),
        );
    }

    /// A bound of the wrong sort is the same failure as the wrong shape.
    #[test]
    #[should_panic(expected = "not a subset of its UInt index extent")]
    fn a_guard_over_the_wrong_value_sort_is_rejected() {
        let mut buf = buffer_with(8);
        buf.release("p", Predicate::LessThanEq(Value::Int(4)));
    }

    /// A producer registering before the frontier moves reads the whole buffer,
    /// including values that arrived before it registered.
    ///
    /// This is a program's own producers, which all enrol during compilation:
    /// anything that arrived while the program was being compiled is still
    /// theirs to read.
    #[test]
    fn a_producer_registering_at_the_start_reads_everything() {
        let mut buf = buffer_with(3);
        buf.release("p", Predicate::False);
        assert_eq!(
            buf.get_elements("p"),
            ColumnValue::from_uints(vec![0, 1, 2])
        );
    }

    /// After the frontier moves, a producer registering from then on reads only
    /// what arrives next.
    ///
    /// This is what stops a replacement version reprocessing the stream: the
    /// operators it rebuilds enrol as new producers, and a source hands a
    /// newly-registered producer everything it still holds.
    #[test]
    fn a_producer_registering_after_the_frontier_reads_only_what_follows() {
        let mut buf = buffer_with(3);
        buf.advance_new_producer_frontier();
        buf.release("late", Predicate::False);
        assert_eq!(
            buf.get_elements("late"),
            ColumnValue::from_uints(Vec::new()),
            "everything already buffered is behind the frontier"
        );

        buf.push(SmolStr::new("e3"));
        assert_eq!(
            buf.get_elements("late"),
            ColumnValue::from_uints(vec![3]),
            "and what arrives next is not"
        );
    }

    /// Moving the frontier does not retroactively change a producer that had
    /// already registered.
    #[test]
    fn moving_the_frontier_leaves_registered_producers_alone() {
        let mut buf = buffer_with(3);
        buf.release("early", Predicate::False);
        buf.advance_new_producer_frontier();
        assert_eq!(
            buf.get_elements("early"),
            ColumnValue::from_uints(vec![0, 1, 2]),
            "the frontier applies at registration, not to whoever is already reading"
        );
    }

    /// A producer that registers past the frontier still holds the buffer: the
    /// prefix is only freed once it has released it too.
    #[test]
    fn a_late_producer_still_counts_toward_the_release_intersection() {
        let mut buf = buffer_with(3);
        buf.release("early", Predicate::False);
        buf.advance_new_producer_frontier();
        buf.release("late", Predicate::False);

        buf.release("early", covering(0, 2));
        assert_eq!(
            buf.start_idx, 3,
            "the late producer registered as having released 0..=2, so the prefix frees"
        );
    }
}
