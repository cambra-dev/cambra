//! A scripted input that grows, drops what it holds released, and notifies, with the regions,
//! steps and generator the consuming-mode tests of the pipeline breakers share.

use std::collections::{BTreeMap, BTreeSet};

use bit_set::BitSet;

use super::test_helpers::{int_entries, keys_between};
use super::*;
use crate::interpreter::{BaseType, ColumnValue, Extent, FunctionGuard, Predicate, Value};

/// The keys of the universe: a model of a guard names a subset of them.
pub(crate) const KEYS: u64 = 12;

pub(crate) fn ints() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(KEYS),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// The value at `key`: a key's value never changes, so a row added twice is the same row.
pub(crate) fn value(key: u64) -> i64 {
    key as i64 * 10
}

/// What an input holds, and what reached it.
#[derive(Default)]
pub(crate) struct Source {
    pub(crate) rows: BTreeMap<u64, i64>,
    pub(crate) pulled: Vec<TileGuard>,
    pub(crate) released: Vec<TileGuard>,
    /// Whether the input states complete only the keys it holds, so that a row may still
    /// arrive at a key it has not answered, until it is [`closed`](Self::closed).
    pub(crate) growing: bool,
    /// Whether no row arrives any more: the input states complete every key it is asked for.
    pub(crate) closed: bool,
    /// The pulls of a region the input had already been released at whole, which answer
    /// nothing and which a breaker that knows the region is released does not make.
    pub(crate) wasted: usize,
    /// How many members a key's group holds, for a [`NestedInput`]: three unless named here.
    pub(crate) members: BTreeMap<u64, usize>,
}

impl Source {
    /// What the input states complete: every key it holds while it grows, and every key once
    /// it is closed or when it does not grow.
    fn statement(&self) -> Predicate {
        match self.growing && !self.closed {
            true => Predicate::from_column_value(&ColumnValue::UInts(
                self.rows.keys().copied().collect(),
            )),
            false => Predicate::True,
        }
    }
}

/// The script of an input, which the test that drives the input writes and the input reads. It
/// is spelled in full like the other test doubles' cells in `test_helpers`, which the
/// shared-state check reads.
#[allow(unused_qualifications)]
pub(crate) type Shared = std::rc::Rc<std::cell::RefCell<Source>>;

/// A source that grows: it states complete only the keys it holds until it is closed.
pub(crate) fn growing_source(keys: impl IntoIterator<Item = u64>) -> Shared {
    let source = source(keys);
    source.borrow_mut().growing = true;
    source
}

pub(crate) fn source(keys: impl IntoIterator<Item = u64>) -> Shared {
    let source = Shared::default();
    for key in keys {
        source.borrow_mut().rows.insert(key, value(key));
    }
    source
}

/// An input that answers its rows less what has been released to it, cut to the guard it is
/// pulled at, and states complete what its [`Source`] states. A row added later in a region it
/// has been released at is dropped, as a producer drops a released region. A pull of a region it
/// has been released at whole is counted in [`Source::wasted`].
pub(crate) struct Input {
    pub(crate) base: ProducerBase,
    pub(crate) source: Shared,
}

impl Input {
    pub(crate) fn over(source: &Shared) -> Self {
        Self {
            base: ProducerBase::unowned(Self::alloc_id(), &ints()),
            source: source.clone(),
        }
    }
}

impl TileProducer for Input {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        self.source.borrow_mut().pulled.push(guard.clone());
        if released_whole(&guard, self.obsolete_guard()) {
            self.source.borrow_mut().wasted += 1;
        }
        let rows = self.source.borrow().rows.clone();
        let mut tile = Tile::data_function(
            ColumnValue::UInts(rows.keys().copied().collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                rows.values().copied().collect(),
            ))),
            self.source.borrow().statement(),
            BitSet::new(),
        );
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile.restrict_to(&guard.projection("Input"), self.tiling());
        tile
    }

    fn release_impl(&mut self, guard: TileGuard) {
        self.source.borrow_mut().released.push(guard);
    }
}

/// Whether `released`, the guard an input has been released at, covers every key `guard` names.
/// A guard naming nothing is not counted.
pub(crate) fn released_whole(guard: &TileGuard, released: &TileGuard) -> bool {
    let wanted = match Projection::of(guard) {
        Ok(Projection::Everything) => Predicate::True,
        Ok(Projection::Keys(keys)) => keys,
        Ok(_) | Err(_) => return false,
    };
    match released {
        guard if guard.is_universal() => true,
        TileGuard::Function(FunctionGuard::Domain(released)) => wanted.minus(released).is_false(),
        TileGuard::Or(arms) => arms.iter().any(|arm| released_whole(guard, arm)),
        _ => false,
    }
}

/// A region of the universe: the guard a consumer hands a breaker, the projection an input
/// notifies, and the keys a model counts.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Region {
    Keys(u64, u64),
    All,
}

impl Region {
    pub(crate) fn guard(self) -> TileGuard {
        match self {
            Keys(first, last) => keys_between(first, last),
            All => ints().universal_guard(),
        }
    }

    pub(crate) fn keys(self) -> BTreeSet<u64> {
        match self {
            Keys(first, last) => (first..=last).collect(),
            All => (0..KEYS).collect(),
        }
    }

    pub(crate) fn projection(self) -> Projection {
        Projection::of(&self.guard()).expect("a region of keys is a projection")
    }
}

pub(crate) fn predicate(guard: &TileGuard) -> Predicate {
    match guard {
        TileGuard::Function(FunctionGuard::Domain(predicate)) => predicate.clone(),
        other => panic!("a guard of the outermost keys, got {other:?}"),
    }
}

pub(crate) fn same_region(a: &Predicate, b: &Predicate) -> bool {
    a.subsumes(b) && b.subsumes(a)
}

/// The keys of the universe `guard` names.
pub(crate) fn keys_of(guard: &TileGuard) -> BTreeSet<u64> {
    let predicate = predicate(guard);
    (0..KEYS)
        .filter(|key| predicate.contains(&Value::UInt(*key)))
        .collect()
}

pub(crate) fn entries(tile: &Tile) -> Vec<(u64, i64)> {
    int_entries(tile)
}

pub(crate) fn rows_of(keys: impl IntoIterator<Item = u64>) -> Vec<(u64, i64)> {
    keys.into_iter().map(|key| (key, value(key))).collect()
}

pub(crate) fn keys_predicate(first: u64, last: u64) -> Predicate {
    predicate(&keys_between(first, last))
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Step {
    /// A row arrives at the input, which drops it when it holds the key's region released.
    Add(u64),
    Notify(Region),
    Consume(Region),
    /// The breaker's consumer releases a region of the breaker's output.
    Release(Region),
    /// No row arrives any more: the input states complete every key it is asked for.
    Close,
}

/// A xorshift generator, seeded: the sequences below are the same on every run.
pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    #[allow(clippy::should_implement_trait)]
    pub(crate) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    pub(crate) fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    pub(crate) fn region(&mut self) -> Region {
        match self.below(8) {
            0 => All,
            _ => {
                let (a, b) = (self.below(KEYS), self.below(KEYS));
                Keys(a.min(b), a.max(b))
            }
        }
    }

    /// A step of a random run. A release names one of `names` half the time, the keys consumed
    /// so far or the groups they fall in, so that it reaches what the breaker holds. A breaker
    /// that listens to no notification draws none.
    pub(crate) fn step_among(&mut self, names: &BTreeSet<u64>, notify: bool) -> Step {
        match self.below(20) {
            0..=5 => Add(self.below(KEYS)),
            6..=7 if notify => Notify(self.region()),
            8 => Close,
            9..=13 => Consume(self.region()),
            _ => Release(self.release_region(names)),
        }
    }

    fn release_region(&mut self, names: &BTreeSet<u64>) -> Region {
        if names.is_empty() || self.below(2) == 0 {
            return self.region();
        }
        let names: Vec<u64> = names.iter().copied().collect();
        let first = names[self.below(names.len() as u64) as usize];
        let last = names[self.below(names.len() as u64) as usize];
        Keys(first.min(last), first.max(last))
    }
}

use Region::{All, Keys};
use Step::{Add, Close, Consume, Notify, Release};

/// The keys a guard has been released at: those of the universe, and whether the keys beyond it,
/// which only the universal guard names.
#[derive(Default)]
pub(crate) struct Released {
    pub(crate) keys: BTreeSet<u64>,
    beyond: bool,
}

impl Released {
    /// Whether releasing `region` adds nothing: the release wrapper passes a release on only when
    /// it grows what is released.
    pub(crate) fn covers(&self, region: Region) -> bool {
        region.keys().is_subset(&self.keys) && (!matches!(region, All) || self.beyond)
    }

    pub(crate) fn add(&mut self, region: Region) {
        self.keys.extend(region.keys());
        self.beyond |= matches!(region, All);
    }
}

/// The predicate naming exactly `keys`.
pub(crate) fn points(keys: impl IntoIterator<Item = u64>) -> Predicate {
    Predicate::from_column_value(&ColumnValue::UInts(keys.into_iter().collect()))
}

/// A model of a growing [`Input`]: the rows it holds, whether it is closed, what it has been
/// released at, and the releases that must have reached it, in order.
#[derive(Default)]
pub(crate) struct InputModel {
    pub(crate) rows: BTreeSet<u64>,
    pub(crate) closed: bool,
    pub(crate) released: Released,
    releases: Vec<Predicate>,
    /// The pulls of a region the input had been released at whole.
    wasted: usize,
}

impl InputModel {
    pub(crate) fn new(initial: &[u64]) -> Self {
        Self {
            rows: initial.iter().copied().collect(),
            ..Self::default()
        }
    }

    /// A row arrives, unless the input is closed. Whether it arrived.
    pub(crate) fn add(&mut self, key: u64) -> bool {
        if self.closed {
            return false;
        }
        self.rows.insert(key);
        true
    }

    /// A pull at `region`: the keys it answers, and what the answer states complete, which the
    /// breaker releases the input at.
    pub(crate) fn pull(&mut self, region: Region) -> (BTreeSet<u64>, Predicate) {
        if self.released.covers(region) {
            self.wasted += 1;
        }
        let keys = region.keys();
        let held: BTreeSet<u64> = self
            .rows
            .iter()
            .copied()
            .filter(|key| keys.contains(key))
            .collect();
        let answered = held
            .iter()
            .copied()
            .filter(|key| !self.released.keys.contains(key))
            .collect();
        let stated = match self.closed {
            true => predicate(&region.guard()),
            false => points(held.iter().copied()),
        };
        let grows = match self.closed {
            true => !self.released.covers(region),
            false => !held.is_subset(&self.released.keys),
        };
        if grows {
            self.releases.push(stated.clone());
        }
        match self.closed {
            true => self.released.add(region),
            false => self.released.keys.extend(held),
        }
        (answered, stated)
    }

    /// The input is released at `region`.
    pub(crate) fn release(&mut self, region: Region) {
        if !self.released.covers(region) {
            self.releases.push(predicate(&region.guard()));
        }
        self.released.add(region);
    }

    /// Whether the input has been released whole, which a pipeline finalizes after.
    pub(crate) fn drained(&self) -> bool {
        self.released.covers(All)
    }

    /// The releases that reached `source`, and its pulls of a region it had been released at
    /// whole, against the model.
    pub(crate) fn check(&self, source: &Shared, trace: &str) {
        let source = source.borrow();
        assert_eq!(
            source.wasted, self.wasted,
            "{trace}: pulls of a region released whole"
        );
        assert_eq!(
            source.released.len(),
            self.releases.len(),
            "{trace}: the input's releases {:?}",
            source.released
        );
        for (actual, expected) in source.released.iter().zip(&self.releases) {
            assert!(
                same_region(&predicate(actual), expected),
                "{trace}: the input is released at {actual:?}, not {expected:?}"
            );
        }
    }
}

/// Groups of three values per key: the nested counterpart of [`ints`].
pub(crate) fn nested_tiling() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(KEYS),
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        ),
    )
}

/// The three values a key's group holds.
pub(crate) fn members(key: u64) -> Vec<i64> {
    members_of(key, 3)
}

/// The first `count` values a key's group holds.
pub(crate) fn members_of(key: u64, count: usize) -> Vec<i64> {
    let base = value(key);
    (0..count as i64).map(|member| base + member).collect()
}

/// An input of groups, one per row of the [`Source`], under the same rules as [`Input`]: it
/// answers the rows it holds less what was released, cut to the guard, each group stated whole.
pub(crate) struct NestedInput {
    pub(crate) base: ProducerBase,
    pub(crate) source: Shared,
    /// Whether the groups are stated open: neither the keys nor what lies beneath them are
    /// complete, so more members may still arrive beneath any key.
    open: bool,
}

impl NestedInput {
    pub(crate) fn over(source: &Shared) -> Self {
        Self {
            base: ProducerBase::unowned(Self::alloc_id(), &nested_tiling()),
            source: source.clone(),
            open: false,
        }
    }

    /// An input whose groups are stated open, so no group is complete.
    pub(crate) fn open_over(source: &Shared) -> Self {
        Self {
            open: true,
            ..Self::over(source)
        }
    }
}

impl TileProducer for NestedInput {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        self.source.borrow_mut().pulled.push(guard.clone());
        if released_whole(&guard, self.obsolete_guard()) {
            self.source.borrow_mut().wasted += 1;
        }
        let source = self.source.borrow();
        let keys: Vec<u64> = source.rows.keys().copied().collect();
        let counts: Vec<usize> = keys
            .iter()
            .map(|key| source.members.get(key).copied().unwrap_or(3))
            .collect();
        let starts: Vec<usize> = counts
            .iter()
            .scan(0, |start, count| {
                let this = *start;
                *start += count;
                Some(this)
            })
            .collect();
        let inner: Vec<u64> = counts.iter().flat_map(|count| 0..*count as u64).collect();
        let values: Vec<i64> = keys
            .iter()
            .zip(&counts)
            .flat_map(|(key, count)| members_of(*key, *count))
            .collect();
        // A group is stated whole only beneath a key the input states complete, so a group that
        // arrives later at another key is not beneath a path the input called complete.
        let (outer, beneath) = match self.open {
            true => (Predicate::False, Predicate::False),
            false => match source.statement() {
                Predicate::True => (Predicate::True, Predicate::True),
                held => (
                    held.clone(),
                    Predicate::Qualified {
                        enclosing: Box::new(held),
                        here: Box::new(Predicate::True),
                    },
                ),
            },
        };
        drop(source);
        let mut tile = Tile::data_function(
            ColumnValue::UInts(keys),
            Box::new(Tile::grouped(
                starts,
                ColumnValue::UInts(inner),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                beneath,
                BitSet::new(),
            )),
            outer,
            BitSet::new(),
        );
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile.restrict_to(&guard.projection("NestedInput"), self.tiling());
        tile
    }

    fn release_impl(&mut self, guard: TileGuard) {
        self.source.borrow_mut().released.push(guard);
    }
}
