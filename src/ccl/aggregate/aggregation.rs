//! The typed fold of one aggregate, and the column of partial aggregations a tile holds.
//!
//! An [`Aggregation`] states an aggregate over Rust types as the `In`/`Agg`/`Out` decomposition
//! of Tangwongsan et al., "General Incremental Sliding-Window Aggregation" (VLDB 2015),
//! Table 1. An [`Accumulator`] is an aggregate with its partial aggregations, one per row, and is
//! what [`Tile::Aggregation`] holds; [`AggregateKind::accumulator`](super::AggregateKind)
//! selects the implementation by kind and element type.
//!
//! Only an [`Accumulator`] seeds, and it seeds its typed state. `Sum` seeds `0` and `Drain` its
//! `unit`, so a fold of no rows still leaves them one row. `Max`, `Min`, and `Sole` have no
//! identity: their state is empty until the first element arrives. An accumulator with no rows
//! has folded nothing, and contributes nothing when combined.

use std::any::Any;
use std::fmt::Debug;
use std::marker::PhantomData;

use bit_vec::BitVec;
use smol_str::SmolStr;

use super::AggregateKind;
use crate::ccl::BaseType;
use crate::interpreter::{ColumnValue, RowIndex, Tile};

/// One aggregate's fold over values of one element type.
pub trait Aggregation: Clone + Debug + PartialEq + Send + Sync {
    /// The kind this implements.
    const KIND: AggregateKind;

    /// The element type of the folded collection.
    type In: Element;
    /// The partial aggregation, `Agg` in the paper.
    type State: StateTile + Clone + Debug + PartialEq + Send + Sync + 'static;
    /// What the aggregate yields once a group is complete.
    type Out: StateTile;

    /// Fold rows `start..end` of `values` into `state`. `None` is the unseeded state, which an
    /// aggregate with an identity seeds before folding, so a fold of no rows still yields it.
    fn accumulate(
        &self,
        state: &mut Option<Self::State>,
        values: &<Self::In as Element>::Column,
        start: RowIndex,
        end: RowIndex,
    );

    /// `combine` in the paper: the partial aggregation of two disjoint parts of a group,
    /// associative.
    fn combine(&self, earlier: Self::State, later: Self::State) -> Self::State;

    /// `lower` in the paper: the output of a finished partial aggregation.
    fn finalize(&self, state: Self::State) -> Self::Out;
}

/// An aggregate with its partial aggregations: one row per group, each the state of one group's
/// fold.
///
/// [`accumulate_tile`](Accumulator::accumulate_tile) acts on the one group of a flat aggregation,
/// a column of at most one row. The other methods are what a tile does to any column it holds.
pub trait Accumulator: Debug + Send + Sync {
    /// The kind of aggregate this runs.
    fn kind(&self) -> AggregateKind;

    /// The number of groups.
    fn rows(&self) -> usize;

    /// Whether no group has been seen.
    fn is_empty(&self) -> bool {
        self.rows() == 0
    }

    /// The cells the partial aggregations hold.
    fn cell_count(&self) -> usize {
        self.rows()
    }

    /// Fold rows `start..end` of `values` into the group, seeding it when it is unseeded.
    fn accumulate_tile(&mut self, values: &Tile, start: RowIndex, end: RowIndex);

    /// Merge `later` into this accumulator. A `whole` merge combines two partial aggregations
    /// of the same group, each at most one row, and one with no rows folded nothing and
    /// contributes nothing, so no identity is created for it. Otherwise `later`'s groups follow
    /// this one's.
    fn merge(&mut self, later: Box<dyn Accumulator>, whole: bool);

    /// The groups `rows` names, in that order and each as often as it appears.
    fn select_rows(&self, rows: &[RowIndex]) -> Box<dyn Accumulator>;

    /// Keep the groups `mask` marks.
    fn retain_rows(&mut self, mask: &BitVec);

    /// The output of every group, one row each.
    fn finalize(self: Box<Self>) -> Tile;

    /// The partial aggregations as a tile, one row each.
    fn to_tile(&self) -> Tile;

    /// The tile the partial aggregations are, for an aggregate whose state is an element of any
    /// shape and so is held as one.
    fn as_tile(&self) -> Option<&Tile> {
        None
    }

    /// [`as_tile`](Accumulator::as_tile), mutably.
    fn as_tile_mut(&mut self) -> Option<&mut Tile> {
        None
    }

    // The plumbing behind `Clone`, `PartialEq`, and `merge`'s downcast, written by `plumbing!`.

    fn clone_box(&self) -> Box<dyn Accumulator>;

    fn eq_dyn(&self, other: &dyn Accumulator) -> bool;

    fn as_any(&self) -> &dyn Any;

    fn into_any(self: Box<Self>) -> Box<dyn Any>;
}

/// The [`Accumulator`] plumbing, the same for every implementation that is `Clone` and
/// `PartialEq`.
macro_rules! plumbing {
    () => {
        fn clone_box(&self) -> Box<dyn Accumulator> {
            Box::new(self.clone())
        }

        fn eq_dyn(&self, other: &dyn Accumulator) -> bool {
            other
                .as_any()
                .downcast_ref::<Self>()
                .is_some_and(|other| self == other)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn into_any(self: Box<Self>) -> Box<dyn Any> {
            self
        }
    };
}

/// `later` as the implementation it must be, since one tile holds one aggregate.
fn same<T: Accumulator + 'static>(later: Box<dyn Accumulator>, kind: AggregateKind) -> T {
    *later
        .into_any()
        .downcast::<T>()
        .unwrap_or_else(|_| panic!("{kind:?} merged with another aggregate"))
}

impl Clone for Box<dyn Accumulator> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

impl PartialEq for dyn Accumulator {
    fn eq(&self, other: &Self) -> bool {
        self.eq_dyn(other)
    }
}

impl Eq for dyn Accumulator {}

/// An element type a column stores, and how a tile of it is read.
pub trait Element: Sized {
    /// What a tile of this element is: a slice, or the bit vector a column of bools is.
    type Column: ?Sized;

    /// The column `values` holds. Panics when `values` is a tile of another type.
    fn column(values: &Tile) -> &Self::Column;
}

/// A state type, and how a tile of it is read and written: one value per row.
pub trait StateTile: Sized {
    /// The value of each row of `state`.
    fn unzip(state: Tile) -> Vec<Self>;

    /// The tile holding one row per value.
    fn zip(states: Vec<Self>) -> Tile;
}

macro_rules! vec_element {
    ($ty:ty, $variant:ident) => {
        impl Element for $ty {
            type Column = [$ty];

            #[inline(always)]
            fn column(values: &Tile) -> &[$ty] {
                match values {
                    Tile::Scalar(ColumnValue::$variant(column)) => column,
                    other => panic!(
                        "expected a column of {}, got {other:?}",
                        stringify!($variant)
                    ),
                }
            }
        }

        impl StateTile for $ty {
            fn unzip(state: Tile) -> Vec<$ty> {
                match state {
                    Tile::Scalar(ColumnValue::$variant(column)) => column,
                    // No rows: a column of whatever type the tile stood empty as.
                    other if other.rows() == 0 => Vec::new(),
                    other => panic!(
                        "expected a column of {}, got {other:?}",
                        stringify!($variant)
                    ),
                }
            }

            fn zip(states: Vec<$ty>) -> Tile {
                Tile::Scalar(ColumnValue::$variant(states))
            }
        }
    };
}

vec_element!(i64, Ints);
vec_element!(u64, UInts);
vec_element!(SmolStr, Strings);

impl Element for bool {
    type Column = BitVec;

    #[inline(always)]
    fn column(values: &Tile) -> &BitVec {
        match values {
            Tile::Scalar(ColumnValue::Bools(column)) => column,
            other => panic!("expected a column of Bools, got {other:?}"),
        }
    }
}

impl StateTile for bool {
    fn unzip(state: Tile) -> Vec<bool> {
        match state {
            Tile::Scalar(ColumnValue::Bools(column)) => column.iter().collect(),
            other if other.rows() == 0 => Vec::new(),
            other => panic!("expected a column of Bools, got {other:?}"),
        }
    }

    fn zip(states: Vec<bool>) -> Tile {
        Tile::Scalar(ColumnValue::Bools(states.into_iter().collect()))
    }
}

/// The `unit`: a state that holds nothing, one per row.
impl StateTile for () {
    fn unzip(state: Tile) -> Vec<()> {
        match state {
            Tile::Scalar(ColumnValue::Units(rows)) => vec![(); rows],
            other if other.rows() == 0 => Vec::new(),
            other => panic!("expected a column of Units, got {other:?}"),
        }
    }

    fn zip(states: Vec<()>) -> Tile {
        Tile::Scalar(ColumnValue::Units(states.len()))
    }
}

/// Elements of any shape, taken as the tile they stand in.
pub(super) struct AnyShape;

impl Element for AnyShape {
    type Column = Tile;

    fn column(values: &Tile) -> &Tile {
        values
    }
}

/// An [`Aggregation`] with its partial aggregations, one per row.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Accum<A: Aggregation> {
    aggregation: A,
    states: Vec<A::State>,
}

impl<A: Aggregation> Accum<A> {
    /// An accumulator over `states`, one row each.
    pub(super) fn new(aggregation: A, states: Vec<A::State>) -> Self {
        Self {
            aggregation,
            states,
        }
    }
}

/// Faults unless each side of a combination is one group's state.
fn one_group_each(kind: AggregateKind, earlier: usize, later: usize) {
    assert!(
        earlier <= 1 && later <= 1,
        "{kind:?} combines two partial aggregations of one group, got {earlier} and {later} rows"
    );
}

impl<A: Aggregation + 'static> Accumulator for Accum<A> {
    plumbing!();

    fn kind(&self) -> AggregateKind {
        A::KIND
    }

    fn rows(&self) -> usize {
        self.states.len()
    }

    fn accumulate_tile(&mut self, values: &Tile, start: RowIndex, end: RowIndex) {
        assert!(
            self.states.len() <= 1,
            "an accumulator folds one group, so it holds at most one row, got {}",
            self.states.len()
        );
        let mut state = self.states.pop();
        self.aggregation
            .accumulate(&mut state, <A::In as Element>::column(values), start, end);
        self.states.extend(state);
    }

    fn merge(&mut self, later: Box<dyn Accumulator>, whole: bool) {
        let mut later = same::<Self>(later, A::KIND);
        if !whole {
            self.states.extend(later.states);
            return;
        }
        one_group_each(A::KIND, self.states.len(), later.states.len());
        match (self.states.pop(), later.states.pop()) {
            (Some(earlier), Some(later)) => {
                self.states.push(self.aggregation.combine(earlier, later))
            }
            (earlier, later) => self.states.extend(earlier.or(later)),
        }
    }

    fn select_rows(&self, rows: &[RowIndex]) -> Box<dyn Accumulator> {
        Box::new(Self::new(
            self.aggregation.clone(),
            rows.iter().map(|&row| self.states[row].clone()).collect(),
        ))
    }

    fn retain_rows(&mut self, mask: &BitVec) {
        debug_assert_eq!(mask.len(), self.states.len(), "a mask has one bit per row");
        let mut keep = mask.iter();
        self.states.retain(|_| keep.next().unwrap_or(false));
    }

    fn finalize(self: Box<Self>) -> Tile {
        let Self {
            aggregation,
            states,
        } = *self;
        <A::Out as StateTile>::zip(
            states
                .into_iter()
                .map(|state| aggregation.finalize(state))
                .collect(),
        )
    }

    fn to_tile(&self) -> Tile {
        <A::State as StateTile>::zip(self.states.clone())
    }
}

/// The running `Sole`: each group's element, held as a tile because an element has any shape,
/// levels included. A group with no element has no row.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct SoleAccum {
    elements: Tile,
}

impl SoleAccum {
    /// An accumulator over `elements`, a row per group that holds one.
    pub(super) fn new(elements: Tile) -> Self {
        Self { elements }
    }
}

impl Accumulator for SoleAccum {
    plumbing!();

    fn kind(&self) -> AggregateKind {
        AggregateKind::Sole
    }

    fn rows(&self) -> usize {
        self.elements.rows()
    }

    fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    fn cell_count(&self) -> usize {
        self.elements.cell_count()
    }

    fn accumulate_tile(&mut self, values: &Tile, start: RowIndex, end: RowIndex) {
        let incoming = end - start;
        admit(self.elements.rows() + incoming);
        if incoming > 0 {
            self.elements
                .merge_rows(values.select_rows(&(start..end).collect::<Vec<_>>()));
        }
    }

    /// A `whole` merge of two seeded states is two elements under one key.
    fn merge(&mut self, later: Box<dyn Accumulator>, whole: bool) {
        let later = same::<Self>(later, AggregateKind::Sole);
        if !whole {
            self.elements.merge_rows(later.elements);
            return;
        }
        one_group_each(
            AggregateKind::Sole,
            self.elements.rows(),
            later.elements.rows(),
        );
        admit(self.elements.rows() + later.elements.rows());
        if self.elements.rows() == 0 {
            self.elements = later.elements;
        }
    }

    fn select_rows(&self, rows: &[RowIndex]) -> Box<dyn Accumulator> {
        Box::new(Self::new(self.elements.select_rows(rows)))
    }

    fn retain_rows(&mut self, mask: &BitVec) {
        self.elements.retain_rows(mask);
    }

    fn finalize(self: Box<Self>) -> Tile {
        self.elements
    }

    fn to_tile(&self) -> Tile {
        self.elements.clone()
    }

    fn as_tile(&self) -> Option<&Tile> {
        Some(&self.elements)
    }

    fn as_tile_mut(&mut self) -> Option<&mut Tile> {
        Some(&mut self.elements)
    }
}

/// Faults unless a `Sole` group holds at most one element.
///
/// Exceeding that means two elements share one key, which is the duplicate a map literal
/// forbids. It is enforced here and not at compile time because only the key values decide it
/// (`src/ccl/design/collections.md`, "Constructor lowering: runtime `groupby` now,
/// constant-folding later").
fn admit(elements: usize) {
    assert!(
        elements <= 1,
        "sole: {elements} elements under one key; a map literal's keys are distinct"
    );
}

/// A use of an [`Aggregation`] whose type [`instantiate`] picks.
pub(super) trait Instantiate {
    type Output;

    fn with<A: Aggregation + 'static>(self, aggregation: A) -> Self::Output;
}

/// The [`Aggregation`] of `kind` over elements of type `base`, handed to `user`. `None` where
/// there is none, and for `Drain` and `Sole`, which are not stated over a column's elements.
pub(super) fn instantiate<I: Instantiate>(
    kind: AggregateKind,
    base: &BaseType,
    user: I,
) -> Option<I::Output> {
    Some(match (kind, base) {
        (AggregateKind::Sum, BaseType::Int) => user.with(Sum),
        (AggregateKind::Max, BaseType::Int) => user.with(Max::<i64>(PhantomData)),
        (AggregateKind::Max, BaseType::UInt) => user.with(Max::<u64>(PhantomData)),
        (AggregateKind::Max, BaseType::String) => user.with(Max::<SmolStr>(PhantomData)),
        (AggregateKind::Max, BaseType::Bool) => user.with(Max::<bool>(PhantomData)),
        (AggregateKind::Min, BaseType::Int) => user.with(Min::<i64>(PhantomData)),
        (AggregateKind::Min, BaseType::UInt) => user.with(Min::<u64>(PhantomData)),
        (AggregateKind::Min, BaseType::String) => user.with(Min::<SmolStr>(PhantomData)),
        (AggregateKind::Min, BaseType::Bool) => user.with(Min::<bool>(PhantomData)),
        _ => return None,
    })
}

/// Builds an [`Accumulator`] over the partial aggregations in a tile, none when it has no rows.
pub(super) struct FromTile(pub(super) Tile);

impl Instantiate for FromTile {
    type Output = Box<dyn Accumulator>;

    fn with<A: Aggregation + 'static>(self, aggregation: A) -> Self::Output {
        Box::new(Accum::new(
            aggregation,
            <A::State as StateTile>::unzip(self.0),
        ))
    }
}

/// The terminal aggregate. Its state is the single `unit` a group of any multiplicity collapses
/// to, so it folds a collection of any element type and ignores the values.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Drain;

impl Aggregation for Drain {
    const KIND: AggregateKind = AggregateKind::Drain;

    type In = AnyShape;
    type State = ();
    type Out = ();

    /// Any fold, of any elements and of none, leaves the group's `unit`.
    fn accumulate(&self, state: &mut Option<()>, _values: &Tile, _start: RowIndex, _end: RowIndex) {
        *state = Some(());
    }

    fn combine(&self, _earlier: (), _later: ()) {}

    fn finalize(&self, _state: ()) {}
}

/// The sum of a group of integers.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Sum;

impl Aggregation for Sum {
    const KIND: AggregateKind = AggregateKind::Sum;

    type In = i64;
    type State = i64;
    type Out = i64;

    fn accumulate(&self, state: &mut Option<i64>, values: &[i64], start: RowIndex, end: RowIndex) {
        let sum = values[start..end].iter().sum::<i64>();
        *state = Some(state.map_or(sum, |held| held + sum));
    }

    #[inline(always)]
    fn combine(&self, earlier: i64, later: i64) -> i64 {
        earlier + later
    }

    #[inline(always)]
    fn finalize(&self, state: i64) -> i64 {
        state
    }
}

/// The greatest element of a group.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Max<T>(pub(super) PhantomData<T>);

/// The least element of a group.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Min<T>(pub(super) PhantomData<T>);

/// `Max` over an ordered element type.
macro_rules! ordered_max {
    ($ty:ty) => {
        impl Aggregation for Max<$ty> {
            const KIND: AggregateKind = AggregateKind::Max;

            type In = $ty;
            type State = $ty;
            type Out = $ty;

            fn accumulate(
                &self,
                state: &mut Option<$ty>,
                values: &[$ty],
                start: RowIndex,
                end: RowIndex,
            ) {
                accumulate_max(state, &values[start..end]);
            }

            #[inline(always)]
            fn combine(&self, earlier: $ty, later: $ty) -> $ty {
                earlier.max(later)
            }

            #[inline(always)]
            fn finalize(&self, state: $ty) -> $ty {
                state
            }
        }
    };
}

/// `Min` over an ordered element type.
macro_rules! ordered_min {
    ($ty:ty) => {
        impl Aggregation for Min<$ty> {
            const KIND: AggregateKind = AggregateKind::Min;

            type In = $ty;
            type State = $ty;
            type Out = $ty;

            fn accumulate(
                &self,
                state: &mut Option<$ty>,
                values: &[$ty],
                start: RowIndex,
                end: RowIndex,
            ) {
                accumulate_min(state, &values[start..end]);
            }

            #[inline(always)]
            fn combine(&self, earlier: $ty, later: $ty) -> $ty {
                earlier.min(later)
            }

            #[inline(always)]
            fn finalize(&self, state: $ty) -> $ty {
                state
            }
        }
    };
}

ordered_max!(i64);
ordered_max!(u64);
ordered_max!(SmolStr);
ordered_min!(i64);
ordered_min!(u64);
ordered_min!(SmolStr);

/// `False < True`, so the maximum is whether any element is `True`.
impl Aggregation for Max<bool> {
    const KIND: AggregateKind = AggregateKind::Max;

    type In = bool;
    type State = bool;
    type Out = bool;

    fn accumulate(
        &self,
        state: &mut Option<bool>,
        values: &BitVec,
        start: RowIndex,
        end: RowIndex,
    ) {
        let any = (start..end).any(|i| values[i]);
        *state = Some(state.is_some_and(|held| held) || any);
    }

    #[inline(always)]
    fn combine(&self, earlier: bool, later: bool) -> bool {
        earlier || later
    }

    #[inline(always)]
    fn finalize(&self, state: bool) -> bool {
        state
    }
}

/// `False < True`, so the minimum is whether every element is `True`.
impl Aggregation for Min<bool> {
    const KIND: AggregateKind = AggregateKind::Min;

    type In = bool;
    type State = bool;
    type Out = bool;

    fn accumulate(
        &self,
        state: &mut Option<bool>,
        values: &BitVec,
        start: RowIndex,
        end: RowIndex,
    ) {
        let all = (start..end).all(|i| values[i]);
        *state = Some(state.is_none_or(|held| held) && all);
    }

    #[inline(always)]
    fn combine(&self, earlier: bool, later: bool) -> bool {
        earlier && later
    }

    #[inline(always)]
    fn finalize(&self, state: bool) -> bool {
        state
    }
}

/// Sets `acc` to the greatest of `values` when that is greater than what it holds, or when it
/// holds nothing.
#[inline(always)]
fn accumulate_max<T: Ord + Clone>(acc: &mut Option<T>, values: &[T]) {
    let Some(max) = values.iter().max() else {
        return;
    };
    match acc {
        Some(held) => {
            if max > held {
                held.clone_from(max);
            }
        }
        None => *acc = Some(max.clone()),
    }
}

/// Sets `acc` to the least of `values` when that is less than what it holds, or when it holds
/// nothing.
#[inline(always)]
fn accumulate_min<T: Ord + Clone>(acc: &mut Option<T>, values: &[T]) {
    let Some(min) = values.iter().min() else {
        return;
    };
    match acc {
        Some(held) => {
            if min < held {
                held.clone_from(min);
            }
        }
        None => *acc = Some(min.clone()),
    }
}
