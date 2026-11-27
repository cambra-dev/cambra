use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::RwLock;
use std::{collections::HashMap, sync::Arc};

use crate::ccl::FieldKey;
use crate::interpreter::CurryLevel;
use crate::interpreter::{Consumer, DataSourceDomainExtentImpl, Projection, dispatcher::Landing};

// The shared consumers this thread is notifying, by address, which `notify_shared` checks a
// notification against to find re-entry.
//
// shared-state-ok: a per-thread record of the consumers a notification is passing through. What
// crosses it is a consumer's address, never a tile.
thread_local! {
    static NOTIFYING: std::cell::RefCell<std::collections::HashSet<usize>> = Default::default();
}

/// Marks a shared consumer as being notified on this thread until it is dropped.
struct Notifying(usize);

impl Notifying {
    /// The mark for `shared`, or `None` where this thread is already notifying it.
    fn enter<C: ?Sized>(shared: &Arc<C>) -> Option<Self> {
        let identity = Arc::as_ptr(shared) as *const () as usize;
        NOTIFYING
            .with(|notifying| notifying.borrow_mut().insert(identity))
            .then_some(Notifying(identity))
    }
}

impl Drop for Notifying {
    fn drop(&mut self) {
        NOTIFYING.with(|notifying| {
            notifying.borrow_mut().remove(&self.0);
        });
    }
}

/// Notify `shared` of the part of `region` it has not been notified of in this landing
/// ([`Landing::unjoined`]). A shared consumer is where an operator's input paths meet, so a push
/// that reaches it by two paths is passed on once. A notification that reaches a shared consumer
/// this thread is already notifying calls [`Landing::reentered`] instead.
///
/// It takes no lock: a consumer guards its own state and releases it before it forwards a
/// notification. Two threads can notify one consumer at once.
pub(crate) fn notify_shared<C: Consumer + ?Sized>(
    shared: &Arc<C>,
    region: &Projection,
    landing: &mut Landing<'_>,
) {
    match Notifying::enter(shared) {
        Some(notifying) => {
            if let Some(region) = landing.unjoined(notifying.0, region) {
                C::notify(shared, &region, landing);
            }
        }
        None => landing.reentered(),
    }
}

/// A consumer handle shared by notification forwarders.
/// It carries notifications, not tile data.
pub type SharedConsumer = Arc<dyn Consumer>;

/// Share a consumer between its input paths. Pipeline entries end notification propagation.
pub fn shared_consumer(consumer: Box<dyn Consumer>) -> SharedConsumer {
    Arc::from(consumer)
}

/// A fresh `Box<dyn Consumer>` forwarding to `shared` — what `subscribe` wants for
/// an input whose notifications should reach the operator's own consumer.
///
/// The consumer forwards every notification as [`Projection::Everything`] ([`widening`]): an
/// input's keys say nothing of the operator's own unless the operator's outermost keys are its
/// input's, which [`forwarding_consumer_keeping_keys`] is for, or its input's under a tag, which
/// [`forwarding_consumer_tagging`] is for.
pub fn forwarding_consumer(shared: &SharedConsumer) -> Box<dyn Consumer> {
    widening(forwarding_consumer_keeping_keys(shared))
}

/// [`forwarding_consumer`] for an input whose outermost keys are the operator's: its region is
/// forwarded as it is.
pub fn forwarding_consumer_keeping_keys(shared: &SharedConsumer) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        shared: shared.clone(),
    })
}

/// [`forwarding_consumer`] for an arm of a tagged union, whose outermost keys are the arm's keys
/// under the arm's tag ([`tagging`]).
pub fn forwarding_consumer_tagging(shared: &SharedConsumer, tag: FieldKey) -> Box<dyn Consumer> {
    tagging(tag, forwarding_consumer_keeping_keys(shared))
}

/// `consumer` behind a consumer that forwards every notification as [`Projection::Everything`].
///
/// An operator passes this to its input in place of its own consumer unless its outermost keys
/// are its input's: the input's region names the input's keys, which say nothing of the
/// operator's own.
pub fn widening(consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(Widening(consumer))
}

/// Preserve notifications above `level` when the value at that level changes shape. A change
/// below it names its enclosing rows.
pub(crate) fn through_values(
    level: CurryLevel,
    downstream: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    if level == CurryLevel::OUTERMOST {
        return widening(downstream);
    }
    Box::new(ThroughValues { level, downstream })
}

struct ThroughValues {
    level: CurryLevel,
    downstream: Box<dyn Consumer>,
}

impl Consumer for ThroughValues {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        self.downstream.notify(&region.above(self.level), landing);
    }
}

struct Widening(Box<dyn Consumer>);

impl Consumer for Widening {
    /// A change widens to every key.
    fn notify(&self, _region: &Projection, landing: &mut Landing<'_>) {
        self.0.notify(&Projection::Everything, landing);
    }
}

/// `consumer` behind a consumer that passes each region on as `restate` names it: an operator that
/// keeps its input's keys under another spelling, as `Uncurry`
/// names an outer and an inner key as one pair, restates both exactly.
pub fn restating(
    restate: Box<dyn Fn(&Projection) -> Projection + Send + Sync>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(Restating(restate, consumer))
}

struct Restating(
    Box<dyn Fn(&Projection) -> Projection + Send + Sync>,
    Box<dyn Consumer>,
);

impl Consumer for Restating {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        self.1.notify(&(self.0)(region), landing);
    }
}

/// `consumer` behind a consumer that forwards each region of the field `name` of a record of
/// values whose fields are `names` as that part of the record ([`Projection::of_field`],
/// normalized by [`Projection::over_fields`]): `MakeRecord` passes this to each operand, since a
/// record of values has no keys and its fields' regions name it field by field.
pub fn fielding(
    name: smol_str::SmolStr,
    names: Vec<smol_str::SmolStr>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(Fielding(name, names, consumer))
}

struct Fielding(smol_str::SmolStr, Vec<smol_str::SmolStr>, Box<dyn Consumer>);

impl Consumer for Fielding {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        if *region != Projection::Nothing {
            let record = Projection::of_field(&self.0, region.clone()).over_fields(&self.1);
            self.2.notify(&record, landing);
        }
    }
}

/// `consumer` behind a consumer that forwards the part of each region of a record of values that
/// names its field `name` ([`Projection::field`]), and nothing for a region naming none of it:
/// `SelectField` passes this to a record of values, whose other fields' regions say nothing of
/// the selected one.
pub fn selecting_field(name: smol_str::SmolStr, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(SelectingField(name, consumer))
}

struct SelectingField(smol_str::SmolStr, Box<dyn Consumer>);

impl Consumer for SelectingField {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let field = region.field(&self.0);
        if field != Projection::Nothing {
            self.1.notify(&field, landing);
        }
    }
}

/// `consumer` behind a consumer that forwards each notification as the same keys under `tag`
/// ([`Projection::tagged`]): an arm of a tagged union passes this to the arm's input, since
/// the union's outermost keys are each arm's keys under the arm's tag.
pub fn tagging(tag: FieldKey, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(Tagging(tag, consumer))
}

struct Tagging(FieldKey, Box<dyn Consumer>);

impl Consumer for Tagging {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        self.1.notify(&region.tagged(&self.0), landing);
    }
}

/// What [`forwarding_consumer_keeping_keys`] returns: it passes each region on as it arrives,
/// through the shared consumer. A wrapper in front of it restates the region ([`widening`],
/// [`tagging`]).
struct Forwarding {
    shared: SharedConsumer,
}

impl Consumer for Forwarding {
    /// A push is passed on at once. A push climbs from one breaker to the next, so
    /// one that re-enters a consumer it is passing through has met a cycle, which fails the run.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        notify_shared(&self.shared, region, landing);
    }
}

/// `consumer` behind a consumer that forwards each region of the input's keys at level `at` as
/// the same paths one level in, with a component beneath the keys above `at` that admits anything:
/// an inverse (`Converse`) at `at` passes this to its input, whose keys at `at` stand beneath the
/// values that become its keys there. Each input key stands beneath exactly one value, so the
/// region names exactly the paths it changed. A region of the keys above `at` is forwarded as it
/// is, since those levels stand.
pub fn one_level_in(at: CurryLevel, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(OneLevelIn { at, consumer })
}

struct OneLevelIn {
    at: CurryLevel,
    consumer: Box<dyn Consumer>,
}

impl OneLevelIn {
    /// `region` one level in, `None` where it names keys beneath level `at`.
    fn restated(&self, region: &Projection) -> Option<Projection> {
        match region {
            Projection::Keys { level, keys } if *level == self.at => Some(Projection::keys_at(
                CurryLevel::new(level.index() + 1),
                keys.with_level_inserted(level.index(), level.index()),
            )),
            Projection::Keys { level, .. } if *level > self.at => None,
            standing => Some(standing.clone()),
        }
    }
}

impl Consumer for OneLevelIn {
    /// A region of the standing levels passes as it is, and one of the keys at level `at` passes
    /// one level in. One that names keys beneath level `at` passes as every key: which output
    /// keys an input row stands beneath depends on its values, which no region carries.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        match self.restated(region) {
            Some(restated) => self.consumer.notify(&restated, landing),
            None => self.consumer.notify(&Projection::Everything, landing),
        }
    }
}

/// Source handles registered by subscriptions, for source-window inspection and route retirement.
#[derive(Default)]
pub struct SourceRegistry {
    source_handles: HashMap<String, Arc<RwLock<dyn DataSourceDomainExtentImpl>>>,
}

impl SourceRegistry {
    pub fn sources(
        &self,
    ) -> impl Iterator<Item = (&str, &Arc<RwLock<dyn DataSourceDomainExtentImpl>>)> + '_ {
        self.source_handles
            .iter()
            .map(|(name, source)| (name.as_str(), source))
    }
    pub fn add_source_handle(&mut self, source: Arc<RwLock<dyn DataSourceDomainExtentImpl>>) {
        let id = source
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get_id()
            .to_string();
        if let Some(existing) = self.source_handles.get(&id) {
            assert!(
                Arc::ptr_eq(existing, &source),
                "two sources are registered as `{id}`"
            );
        } else {
            self.source_handles.insert(id, source);
        }
    }
    pub fn forget_source(&mut self, id: &str) {
        self.source_handles.remove(id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{RegionLog, keys_between};

    /// A row's items leave the arm's record once the arm delivers the row whole, and a later
    /// delivery for another row keeps the record a region of keys.
    #[test]
    fn a_row_delivered_whole_leaves_the_record() {
        use crate::interpreter::{CurryLevel, Predicate, Value};
        let row = |k| Predicate::point(Value::UInt(k));
        let item = |k, i| {
            Projection::keys_at(
                CurryLevel::new(1),
                Predicate::qualified(row(k), Predicate::point(Value::UInt(i))),
            )
        };
        let field = FieldBeneathRows {
            name: "history".into(),
            rows: CurryLevel::OUTERMOST,
        };
        let mut deliveries = ZipDeliveries {
            announced: Predicate::False,
            items: HashMap::new(),
        };
        deliveries.arrival(0, &field, &item(7, 0), &item(7, 0), &row(7));
        let closing = Projection::keys_at(
            CurryLevel::new(1),
            Predicate::qualified(row(7), Predicate::True),
        );
        deliveries.arrival(0, &field, &closing, &closing, &row(7));
        deliveries.arrival(0, &field, &item(8, 0), &item(8, 0), &row(8));
        let Projection::Keys { keys, .. } = &deliveries.items[&0] else {
            panic!(
                "an arm's record is a region of keys: {:?}",
                deliveries.items[&0]
            )
        };
        assert!(
            !keys.contains_path(&[Value::UInt(7), Value::UInt(0)]),
            "{keys:?}"
        );
        assert!(
            keys.contains_path(&[Value::UInt(8), Value::UInt(0)]),
            "{keys:?}"
        );
    }

    /// Item deliveries at two levels beneath the rows union to keys at the deeper level, which
    /// is what `ZipDeliveries::arrival` reads the closed rows off.
    #[test]
    fn deliveries_at_two_levels_union_to_keys() {
        use crate::interpreter::{CurryLevel, Predicate, Value};
        let row = |k| Predicate::point(Value::UInt(k));
        let at_items = Projection::keys_at(
            CurryLevel::new(1),
            Predicate::qualified(row(7), Predicate::True),
        );
        let at_days = Projection::keys_at(
            CurryLevel::new(2),
            Predicate::qualified(
                Predicate::qualified(row(8), Predicate::True),
                Predicate::point(Value::UInt(0)),
            ),
        );
        let seen = at_items.union(&at_days);
        let Projection::Keys { level, keys } = &seen else {
            panic!("the union of key deliveries is keys: {seen:?}")
        };
        let closed = (0..level.index()).fold(keys.clone(), |keys, _| keys.rows_whole_beneath());
        assert!(closed.contains_path(&[Value::UInt(7)]), "{seen:?}");
        assert!(!closed.contains_path(&[Value::UInt(8)]), "{seen:?}");
    }

    #[test]
    fn a_replaced_whole_value_walks_a_widened_route() {
        use crate::interpreter::dispatcher::PipelineId;
        struct Entry;
        impl Consumer for Entry {
            fn notify(&self, _: &Projection, landing: &mut Landing<'_>) {
                landing.queue(
                    PipelineId(0),
                    &crate::interpreter::TileGuard::Scalar(crate::interpreter::Predicate::True),
                );
            }
        }
        let consumer = through_values(CurryLevel::OUTERMOST, Box::new(Entry));
        let mut landing = Landing::route();
        consumer.notify(
            &Projection::admitting(crate::interpreter::Predicate::point(
                crate::interpreter::Value::UInt(0),
            )),
            &mut landing,
        );
        let reached = landing.routes();
        assert_eq!(reached.len(), 1);
    }

    /// What a broadcast pairing at level 1 announces for a delivery of `region` on its constant
    /// side, after `rows` were delivered on its row side.
    fn constant_side_announces(rows: &[u64], region: &Projection) -> Projection {
        use crate::interpreter::{Predicate, Value};
        let at = CurryLevel::new(1);
        let delivered = nothing_delivered(true, true);
        let (row_log, row_announced) = RegionLog::new();
        let row_side = pairing(
            PairingSide::Rows(Partners::ConstantKeys),
            at,
            delivered.clone(),
            Box::new(row_log),
        );
        for row in rows {
            let row = Projection::admitting(Predicate::point(Value::UInt(*row)));
            crate::interpreter::dispatcher::notify_for_test(&*row_side, &row);
        }
        assert!(
            row_announced
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty(),
            "no partner has arrived, so a row completes no pair"
        );
        let (log, announced) = RegionLog::new();
        let constant_side = pairing(PairingSide::ConstantKeys, at, delivered, Box::new(log));
        crate::interpreter::dispatcher::notify_for_test(&*constant_side, region);
        let announced = announced.read().unwrap_or_else(PoisonError::into_inner);
        Projection::any_of(announced.iter().cloned())
    }

    /// A constant side's delivery that mixes whole keys with part of another key's values
    /// announces what its arms announce delivered one by one: before any row arrives nothing,
    /// and after row 5 arrives only pairs beneath row 5. A whole-key arm is cut by the rows
    /// delivered as a lone whole-key delivery is.
    #[test]
    fn a_mixed_delivery_announces_what_its_arms_announce_separately() {
        use crate::interpreter::{Predicate, Value};
        let key = |k: u64| Predicate::point(Value::UInt(k));
        let whole = Projection::admitting(key(0));
        let part = Projection::within(
            CurryLevel::OUTERMOST,
            key(1),
            Projection::of_field("a", Projection::Everything),
        );
        let mixed = Projection::any_of([whole.clone(), part.clone()]);
        assert!(matches!(mixed, Projection::Or(_)), "{mixed:?}");
        for rows in [&[][..], &[5]] {
            let separate = Projection::any_of([
                constant_side_announces(rows, &whole),
                constant_side_announces(rows, &part),
            ]);
            assert_eq!(
                constant_side_announces(rows, &mixed),
                separate,
                "rows {rows:?}"
            );
        }
        assert_eq!(constant_side_announces(&[], &mixed), Projection::Nothing);
        let under_5 = |k: u64| Predicate::qualified(key(5), key(k));
        assert_eq!(
            constant_side_announces(&[5], &mixed),
            Projection::any_of([
                Projection::keys_at(CurryLevel::new(1), under_5(0)),
                Projection::within(
                    CurryLevel::new(1),
                    under_5(1),
                    Projection::of_field("a", Projection::Everything)
                ),
            ])
        );
    }

    // Selecting a collection from a grouped record exposes its item keys as the
    // Product's paired level. Either the group row or its item can arrive first.
    #[rstest::rstest]
    fn a_nested_group_item_announces_only_its_pair(#[values(false, true)] item_first: bool) {
        use crate::interpreter::dispatcher::notify_for_test;
        use crate::interpreter::{Predicate, Value};
        let at = CurryLevel::new(2);
        let group_path = [Value::Bool(true), Value::Bool(false)];
        let group = Projection::of_path(&group_path);
        let item = Projection::within(
            CurryLevel::new(1),
            Predicate::exactly(&group_path),
            Projection::of_field(
                "_0",
                Projection::of_field(
                    "_0",
                    Projection::admitting(Predicate::point(Value::UInt(3))),
                ),
            ),
        );
        let delivered = nothing_delivered(true, true);
        let (log, received) = RegionLog::new();
        let log = shared_consumer(Box::new(log));
        let rows = pairing(
            PairingSide::Rows(Partners::Paths),
            at,
            delivered.clone(),
            forwarding_consumer_keeping_keys(&log),
        );
        let items = selecting_field_beneath_keys(
            "_0".into(),
            selecting_field_beneath_keys(
                "_0".into(),
                pairing(
                    PairingSide::Paths,
                    at,
                    delivered,
                    forwarding_consumer_keeping_keys(&log),
                ),
            ),
        );
        let row = (&*rows, &group);
        let item = (&*items, &item);
        let [first, second] = if item_first { [item, row] } else { [row, item] };
        notify_for_test(first.0, first.1);
        assert!(
            received
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
        notify_for_test(second.0, second.1);
        assert_eq!(
            *received.read().unwrap_or_else(PoisonError::into_inner),
            [Projection::of_path(&[
                Value::Bool(true),
                Value::Bool(false),
                Value::UInt(3)
            ]),]
        );
    }

    #[test]
    fn forwarding_preserves_each_region_and_widening_names_the_whole_input() {
        let (log, received) = RegionLog::new();
        let shared = shared_consumer(Box::new(log));
        let keys = Projection::of(&keys_between(2, 4)).unwrap();
        crate::interpreter::dispatcher::notify_for_test(
            &*forwarding_consumer_keeping_keys(&shared),
            &keys,
        );
        crate::interpreter::dispatcher::notify_for_test(&*forwarding_consumer(&shared), &keys);
        assert_eq!(
            *received.read().unwrap_or_else(PoisonError::into_inner),
            [keys, Projection::Everything]
        );
    }
}

/// What each input of a pairing operator has delivered, which its notifications restate a delta
/// against: the rows a pair hangs under, and what pairs them with those rows.
///
/// A pairing operator's output path `(𝑟, 𝑘)` exists once both its halves have arrived, so a
/// delivery on one input creates exactly the pairs of its delta with what the other input has
/// delivered: Δ𝑅 × 𝐾 ∪ 𝑅 × Δ𝐾. Each pair is announced once, by the delivery that completes
/// it, so no announcement names a pair before both halves exist. `rows` admits paths of the
/// level above the pairs; `partners` admits the constant's keys for a broadcast
/// ([`Partners::ConstantKeys`]) and the pairs' own paths for a row-aligned pairing
/// ([`Partners::Paths`]). Both grow only on a delivery ([`Landing::is_delivery`]): a planner's
/// walk restates as though every partner had arrived, so the route it reads keeps keys.
pub(crate) struct Delivered {
    rows: crate::interpreter::Predicate,
    partners: crate::interpreter::Predicate,
}

/// What a delivery adds to a pairing's [`Delivered`], applied once its pairs are announced.
type RecordDelivery = Box<dyn FnOnce(&mut Delivered)>;

/// [`Delivered`], shared by the consumers in front of one pairing operator's inputs.
// shared-state-ok: the regions a pairing's inputs have delivered, which the consumers in front of
// its inputs read and grow on each delivery; what crosses it is predicates, never a tile.
pub(crate) type SharedDelivered = Arc<Mutex<Delivered>>;

/// A [`Delivered`] with nothing delivered yet of a side whose keys arrive by a push, and
/// everything of a side no push reaches, which holds all its keys from the start
/// ([`TileOperator::keys_arrive_by_push`](crate::interpreter::tile_operators::TileOperator::keys_arrive_by_push)).
pub(crate) fn nothing_delivered(rows_arrive: bool, partners_arrive: bool) -> SharedDelivered {
    let held = |arrive: bool| match arrive {
        true => crate::interpreter::Predicate::False,
        false => crate::interpreter::Predicate::True,
    };
    Arc::new(Mutex::new(Delivered {
        rows: held(rows_arrive),
        partners: held(partners_arrive),
    }))
}

/// What a pairing's partner side holds ([`Delivered::partners`]).
#[derive(Clone, Copy)]
pub(crate) enum Partners {
    /// The keys of a constant broadcast beneath every row (`MapResultToConst`): a pair is a
    /// row with one constant key, so the pairs are every delivered row by every delivered key.
    ConstantKeys,
    /// The pairs' own paths, delivered by a side aligned with the rows (`Product`'s inner side):
    /// a pair exists where that side holds it and the row side has delivered its row.
    Paths,
}

/// Which input of a pairing a consumer sits in front of.
#[derive(Clone, Copy)]
pub(crate) enum PairingSide {
    /// The rows: a region of rows announces those rows' pairs with the partners delivered.
    Rows(Partners),
    /// A constant's keys (`Partners::ConstantKeys`): a region of keys announces every
    /// delivered row's pair with them. A region beneath the constant's outermost keys widens.
    ConstantKeys,
    /// The aligned side's pairs (`Partners::Paths`): a region of pairs announces those whose
    /// row has been delivered. A region beneath the pairs passes on as it is.
    Paths,
}

/// `consumer` behind a consumer that restates a delta of one input of a pairing operator as the
/// pairs it creates, at level `at` ([`Delivered`]).
pub(crate) fn pairing(
    side: PairingSide,
    at: CurryLevel,
    delivered: SharedDelivered,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(Pairing {
        side,
        at,
        delivered,
        consumer,
    })
}

struct Pairing {
    side: PairingSide,
    at: CurryLevel,
    delivered: SharedDelivered,
    consumer: Box<dyn Consumer>,
}

/// What each arm of a row-aligned operator has delivered of the keys its arms share, as paths of
/// that level. A row of the output exists once every arm has delivered it, so a delivery on one
/// arm announces the part of its region under the rows every other arm has delivered: Δ𝑅ᵢ ∩
/// ⋂ⱼ≠ᵢ 𝑅ⱼ. The arm that delivers a row last announces it. An arm no push reaches holds every
/// row from the start
/// ([`TileOperator::keys_arrive_by_push`](crate::interpreter::tile_operators::TileOperator::keys_arrive_by_push)).
/// Each arm's record grows only on a delivery ([`Landing::is_delivery`]).
pub(crate) struct AlignedDelivered {
    arms: Vec<crate::interpreter::Predicate>,
    /// Only a zip pairing at the outer row level distinguishes individual field arrivals.
    zip: Option<Box<ZipDeliveries>>,
}

/// [`AlignedDelivered`], shared by the consumers in front of one operator's arms.
// shared-state-ok: the rows each arm has delivered, which the consumers in front of the arms read
// and grow on each delivery; what crosses it is predicates, never a tile.
type SharedAligned = Arc<Mutex<AlignedDelivered>>;

/// How the region of an input of a row-aligned operator names the operator's rows
/// ([`AlignedInputs::consumer`]).
#[derive(Clone, Copy)]
pub(crate) enum InputRows {
    /// The input's keys are the operator's, so its region names the operator's rows.
    Keys,
    /// The operator reads the input whole at every row, so any region of it names every row.
    Whole,
}

/// The consumers in front of the inputs of one operator whose row exists once every input has
/// delivered it ([`AlignedDelivered`]), at level `at`: `Zip`, `Filter`, a flat `Union`,
/// `MapResult`, `MapResultToConst` at the outermost level, and `CheckedLookup`. Each operator that
/// joins inputs at shared rows builds one, so a row is announced once, by the delivery that
/// completes it. A pairing operator restates deliveries as pairs instead ([`Delivered`]).
pub(crate) struct AlignedInputs {
    at: CurryLevel,
    delivered: SharedAligned,
}

impl AlignedInputs {
    /// For `inputs` in arm order. An input whose keys arrive by no push holds every row from the
    /// start
    /// ([`TileOperator::keys_arrive_by_push`](crate::interpreter::tile_operators::TileOperator::keys_arrive_by_push)).
    pub(crate) fn new<'a>(
        at: CurryLevel,
        inputs: impl IntoIterator<Item = &'a Arc<dyn crate::interpreter::tile_operators::TileOperator>>,
    ) -> Self {
        let arms = inputs
            .into_iter()
            .map(|input| match input.keys_arrive_by_push() {
                true => crate::interpreter::Predicate::False,
                false => crate::interpreter::Predicate::True,
            })
            .collect();
        Self {
            at,
            delivered: Arc::new(Mutex::new(AlignedDelivered { arms, zip: None })),
        }
    }

    /// A zip arm maps later item arrivals to its own field of already joined rows.
    pub(crate) fn zip_field(
        &self,
        arm: usize,
        name: smol_str::SmolStr,
        consumer: Box<dyn Consumer>,
    ) -> Box<dyn Consumer> {
        Box::new(Aligned {
            arm,
            at: self.at,
            delivered: self.delivered.clone(),
            field: Some(FieldBeneathRows {
                name,
                rows: self.at,
            }),
            consumer,
        })
    }

    /// `consumer` behind the consumer of input `arm`, which passes on a delivery only under the
    /// rows every other input has delivered. A region of an input read whole names every row
    /// (`rows`).
    pub(crate) fn consumer(
        &self,
        arm: usize,
        rows: InputRows,
        consumer: Box<dyn Consumer>,
    ) -> Box<dyn Consumer> {
        let aligned = Box::new(Aligned {
            arm,
            at: self.at,
            delivered: self.delivered.clone(),
            field: None,
            consumer,
        });
        match rows {
            InputRows::Keys => aligned,
            InputRows::Whole => widening(aligned),
        }
    }
}

struct Aligned {
    arm: usize,
    at: CurryLevel,
    delivered: SharedAligned,
    field: Option<FieldBeneathRows>,
    consumer: Box<dyn Consumer>,
}

/// The rows of level `at` that `region` reaches, as paths of that level: its keys at `at`, the
/// paths beneath its keys above `at`, and the paths its keys beneath `at` run through. `None` where
/// the region names fields of a record, which name no row.
fn rows_reached(region: &Projection, at: CurryLevel) -> Option<crate::interpreter::Predicate> {
    use crate::interpreter::Predicate;
    match region {
        Projection::Everything => Some(Predicate::True),
        Projection::Nothing => Some(Predicate::False),
        Projection::Fields { .. } => None,
        Projection::Or(arms) => arms.iter().try_fold(Predicate::False, |rows, arm| {
            Some(rows.union(&rows_reached(arm, at)?))
        }),
        Projection::Keys { level, keys } | Projection::Within { level, keys, .. } => {
            match *level > at {
                true => rows_reached(
                    &Projection::keys_at(*level, keys.clone())
                        .above(CurryLevel::new(at.index() + 1)),
                    at,
                ),
                false => paths_at(&Projection::keys_at(*level, keys.clone()), at),
            }
        }
    }
}

impl Consumer for Aligned {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let rows = |r: &Projection| match &self.field {
            Some(field) => field.restated(r).rows(),
            None => r.clone(),
        };
        if !landing.is_delivery() {
            self.consumer.notify(&rows(region), landing);
            return;
        }
        let Some(delta) = rows_reached(region, self.at) else {
            self.consumer.notify(&rows(region), landing);
            return;
        };
        // The other arms are read and the delta recorded under one lock, so of two deliveries on
        // different threads the later one announces each row they complete.
        let mut delivered = self
            .delivered
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let others = delivered
            .arms
            .iter()
            .enumerate()
            .filter(|(arm, _)| *arm != self.arm)
            .fold(crate::interpreter::Predicate::True, |rows, (_, arm)| {
                rows.intersect(arm)
            });
        let own = &mut delivered.arms[self.arm];
        *own = own.union(&delta);
        let arrived = if others.is_true() {
            region.clone()
        } else {
            region.intersect(&Projection::keys_at(self.at, others.clone()))
        };
        let restated = match &self.field {
            Some(field) if self.at == CurryLevel::OUTERMOST => {
                let zip = delivered.zip.get_or_insert_with(|| {
                    Box::new(ZipDeliveries {
                        announced: crate::interpreter::Predicate::False,
                        items: HashMap::new(),
                    })
                });
                zip.arrival(self.arm, field, region, &arrived, &delta.intersect(&others))
            }
            Some(field) => field.restated(&arrived).rows(),
            None => arrived,
        };
        drop(delivered);
        if restated == Projection::Nothing {
            return;
        }
        self.consumer.notify(&restated, landing);
    }
}

/// `consumer` behind a consumer that passes on a region of a record of values, whose fields arrive
/// independently, only once every field has delivered: from the delivery that completes the
/// record on. A reader that computes from the whole record has nothing to read before then, and a
/// delivery of one field is otherwise passed on once per field. `fields` names each field and
/// whether it arrives by a push; one that does not holds its value from the start. Each field's
/// record grows only on a delivery ([`Landing::is_delivery`]).
pub(crate) fn whole_once_complete(
    fields: Vec<(smol_str::SmolStr, bool)>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    let delivered = fields.iter().map(|(_, arrives)| !arrives).collect();
    Box::new(WholeOnceComplete {
        names: fields.into_iter().map(|(name, _)| name).collect(),
        delivered: Mutex::new(delivered),
        consumer,
    })
}

struct WholeOnceComplete {
    names: Vec<smol_str::SmolStr>,
    // shared-state-ok: which of the record's fields have delivered, set by each field's
    // notification on any worker thread; what crosses it is one flag per field, never a tile.
    delivered: Mutex<Vec<bool>>,
    consumer: Box<dyn Consumer>,
}

impl Consumer for WholeOnceComplete {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        if !landing.is_delivery() {
            self.consumer.notify(region, landing);
            return;
        }
        let complete = {
            let mut delivered = self
                .delivered
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            for (name, field) in self.names.iter().zip(delivered.iter_mut()) {
                *field |= region.field(name) != Projection::Nothing;
            }
            delivered.iter().all(|field| *field)
        };
        if complete {
            self.consumer.notify(region, landing);
        }
    }
}

/// `consumer` behind a consumer that forwards a region of a stream of records as the region of the
/// selected field `name`: the same keys, and of a region within the records' values the part of
/// the field `name` ([`Projection::field`]), and nothing for a part naming none of it.
/// `SelectField` passes this to a stream of records, whose keys are the selected field's.
pub fn selecting_field_beneath_keys(
    name: smol_str::SmolStr,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(SelectingFieldBeneathKeys(name, consumer))
}

struct SelectingFieldBeneathKeys(smol_str::SmolStr, Box<dyn Consumer>);

impl SelectingFieldBeneathKeys {
    fn restated(&self, region: &Projection) -> Projection {
        match region {
            Projection::Within {
                level,
                keys,
                values,
            } => Projection::within(*level, keys.clone(), values.field(&self.0)),
            Projection::Or(arms) => Projection::any_of(arms.iter().map(|arm| self.restated(arm))),
            whole => whole.clone(),
        }
    }
}

impl Consumer for SelectingFieldBeneathKeys {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let restated = self.restated(region);
        if restated == Projection::Nothing
            && *region != Projection::Nothing
            && landing.is_delivery()
        {
            return;
        }
        self.1.notify(&restated, landing);
    }
}

/// The first delivery to match a row announces all its fields. Subsequent item deliveries
/// announce their field alone until the accumulated items cover the field's entire domain.
struct ZipDeliveries {
    announced: crate::interpreter::Predicate,
    /// Per arm, the item deliveries of the arm's rows. A row the arm delivers whole, and a matched
    /// row whose items have closed, leave it, since no later item delivery reaches them.
    items: HashMap<usize, Projection>,
}

impl ZipDeliveries {
    fn arrival(
        &mut self,
        arm: usize,
        field: &FieldBeneathRows,
        region: &Projection,
        arrived: &Projection,
        matched: &crate::interpreter::Predicate,
    ) -> Projection {
        let first = matched.minus(&self.announced);
        self.announced = self.announced.union(matched);
        let Projection::Keys { level, keys } = region else {
            return field.restated(arrived).rows();
        };
        if *level == field.rows {
            // The arm delivered these rows whole, so their items leave the record.
            if let Some(seen) = self.items.get_mut(&arm) {
                *seen = seen.minus(&Projection::keys_at(field.rows, keys.clone()));
            }
            return field.restated(arrived).rows();
        }
        // Keep even arrivals before the other arm reaches the row. The last item or an
        // empty remainder can complete the field without a row-level notification.
        let seen = self.items.entry(arm).or_insert(Projection::Nothing);
        *seen = seen.union(region);
        let closed = match &*seen {
            Projection::Everything => crate::interpreter::Predicate::True,
            Projection::Keys { level, keys } => {
                (0..level.index()).fold(keys.clone(), |keys, _| keys.rows_whole_beneath())
            }
            _ => unreachable!("the union of nonempty key deliveries is keys or everything"),
        };
        let whole_rows = first.union(&matched.intersect(&closed));
        // A matched row whose items closed takes no further item delivery, so its items leave.
        *seen = seen.minus(&Projection::keys_at(field.rows, matched.intersect(&closed)));
        let whole = Projection::keys_at(field.rows, whole_rows);
        whole.union(&field.restated(&arrived.minus(&whole)))
    }
}

struct FieldBeneathRows {
    name: smol_str::SmolStr,
    rows: CurryLevel,
}

impl FieldBeneathRows {
    /// The region of the record's rows `region`, a region of the field's own tiling, names.
    fn restated(&self, region: &Projection) -> Projection {
        let of_field = |part: Projection| {
            Projection::fields(
                [(self.name.clone(), part)].into_iter().collect(),
                Projection::Nothing,
            )
        };
        match region {
            Projection::Nothing => Projection::Nothing,
            Projection::Everything => Projection::within(
                self.rows,
                crate::interpreter::Predicate::True,
                of_field(Projection::Everything),
            ),
            // Keys at or above the rows name the field of every row beneath them.
            Projection::Keys { level, keys } if *level <= self.rows => Projection::within(
                self.rows,
                keys.descend(self.rows.index() - level.index()),
                of_field(Projection::Everything),
            ),
            Projection::Keys { level, keys } => {
                let relative = level.index() - self.rows.index() - 1;
                Projection::any_of(split_beneath_rows(keys, relative).into_iter().map(
                    |(rows, part)| {
                        Projection::within(
                            self.rows,
                            rows,
                            of_field(Projection::keys_at(CurryLevel::new(relative), part)),
                        )
                    },
                ))
            }
            Projection::Or(arms) => Projection::any_of(arms.iter().map(|arm| self.restated(arm))),
            // A part of the field's values beneath its own keys: those keys are the rows' where they
            // stand at the rows' level, and keys within the field's values beneath them otherwise.
            Projection::Within {
                level,
                keys,
                values,
            } if *level == self.rows => {
                Projection::within(self.rows, keys.clone(), of_field((**values).clone()))
            }
            Projection::Within {
                level,
                keys,
                values,
            } if *level > self.rows => {
                let relative = level.index() - self.rows.index() - 1;
                Projection::any_of(split_beneath_rows(keys, relative).into_iter().map(
                    |(rows, part)| {
                        Projection::within(
                            self.rows,
                            rows,
                            of_field(Projection::within(
                                CurryLevel::new(relative),
                                part,
                                (**values).clone(),
                            )),
                        )
                    },
                ))
            }
            other => panic!("{other:?} names a part this field's rows have no spelling for"),
        }
    }
}

/// The pairs of rows and paths beneath them `paths` admits, `paths` being over paths `relative`
/// levels beneath the rows' level: each arm split into the rows above and the paths beneath them.
/// An unqualified arm stands beneath every row.
fn split_beneath_rows(
    paths: &crate::interpreter::Predicate,
    relative: usize,
) -> Vec<(crate::interpreter::Predicate, crate::interpreter::Predicate)> {
    use crate::interpreter::Predicate;
    match paths {
        Predicate::False => Vec::new(),
        Predicate::Or(arms) => arms
            .iter()
            .flat_map(|arm| split_beneath_rows(arm, relative))
            .collect(),
        Predicate::Qualified { enclosing, here } if relative == 0 => {
            vec![((**enclosing).clone(), (**here).clone())]
        }
        Predicate::Qualified { enclosing, here } => split_beneath_rows(enclosing, relative - 1)
            .into_iter()
            .map(|(rows, above)| (rows, Predicate::qualified(above, (**here).clone())))
            .collect(),
        unqualified => vec![(Predicate::True, unqualified.clone())],
    }
}

/// `consumer` behind a consumer in front of the input of an operator that computes each value
/// anew from the input's value at the same key, as `MapResult` applies its function: a region of
/// keys passes on unchanged, and a region naming part of some values as the rows it runs through.
pub fn whole_values_at(consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(WholeValuesAt(consumer))
}

struct WholeValuesAt(Box<dyn Consumer>);

impl Consumer for WholeValuesAt {
    /// A region of keys passes on unchanged: the function keeps the input's keys and computes the
    /// values beneath them. A region naming part of some values names the input's values, which
    /// the function replaces, so it passes on as the rows it runs through: the value there is
    /// read again whole, and what of it is final is stated in the tile the reader pulls.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        match region.names_part_of_values() {
            false => self.0.notify(region, landing),
            true => self.0.notify(&region.rows(), landing),
        }
    }
}

/// The outermost keys the paths `keys`, `levels` levels beneath them, run through.
fn outermost_keys(
    keys: &crate::interpreter::Predicate,
    levels: usize,
) -> crate::interpreter::Predicate {
    use crate::interpreter::Predicate;
    match keys {
        _ if levels == 0 => keys.clone(),
        Predicate::Or(arms) => arms
            .iter()
            .map(|arm| outermost_keys(arm, levels))
            .fold(Predicate::False, |all, arm| all.union(&arm)),
        Predicate::Qualified { enclosing, .. } => outermost_keys(enclosing, levels - 1),
        _ => Predicate::True,
    }
}

/// The arms of `region`, which an `Or` holds and any other region is one of.
fn region_arms(region: &Projection) -> Vec<Projection> {
    match region {
        Projection::Or(arms) => arms.clone(),
        single => vec![single.clone()],
    }
}

/// `region`'s keys as a predicate over the paths of level `to`, `None` where the region names
/// only part of a value there. A region above `to` admits every path beneath its keys;
/// a collection selected within a group qualifies its item paths by that group.
fn paths_at(region: &Projection, to: CurryLevel) -> Option<crate::interpreter::Predicate> {
    use crate::interpreter::Predicate;
    let (mut level, mut keys) = match region {
        Projection::Within {
            level,
            keys,
            values,
        } if *level < to => {
            let below = to.index() - level.index() - 1;
            let paths = paths_at(values, CurryLevel::new(below))?;
            return Some(crate::interpreter::tiling::beneath_keys(
                &paths, keys, below,
            ));
        }
        Projection::Within { .. } => return None,
        Projection::Or(arms) => {
            return arms.iter().try_fold(Predicate::False, |paths, arm| {
                Some(paths.union(&paths_at(arm, to)?))
            });
        }
        Projection::Everything => return Some(Predicate::True),
        Projection::Nothing => return Some(Predicate::False),
        Projection::Keys { level, keys } => (level.index(), keys.clone()),
        // A region of a record's fields names no keys of the rows.
        Projection::Fields { .. } => return None,
    };
    if level > to.index() {
        return None;
    }
    while level < to.index() {
        keys = Predicate::qualified(keys, Predicate::True);
        level += 1;
    }
    Some(keys)
}

impl Pairing {
    /// The pairs `region` creates and what it adds to [`Delivered`], `None` where the region
    /// names keys beneath what the side restates. `recorded` says the region is a delivery.
    fn pairs(
        &self,
        region: &Projection,
        recorded: bool,
        delivered: &Delivered,
    ) -> Option<(crate::interpreter::Predicate, RecordDelivery)> {
        use crate::interpreter::Predicate;
        let rows_level = self
            .at
            .enclosing()
            .expect("a pairing pairs beneath a level of rows");
        let (rows, partners) = match recorded {
            true => (delivered.rows.clone(), delivered.partners.clone()),
            false => (Predicate::True, Predicate::True),
        };
        Some(match self.side {
            PairingSide::Rows(against) => {
                let delta = paths_at(&region.above(self.at), rows_level)?;
                let pairs = match against {
                    Partners::ConstantKeys => Predicate::qualified(delta.clone(), partners),
                    Partners::Paths => {
                        Predicate::qualified(delta.clone(), Predicate::True).intersect(&partners)
                    }
                };
                let record: RecordDelivery =
                    Box::new(move |seen| seen.rows = seen.rows.union(&delta));
                (pairs, record)
            }
            PairingSide::ConstantKeys => {
                let delta = paths_at(region, CurryLevel::OUTERMOST)?;
                let pairs = Predicate::qualified(rows, delta.clone());
                let record: RecordDelivery =
                    Box::new(move |seen| seen.partners = seen.partners.union(&delta));
                (pairs, record)
            }
            PairingSide::Paths => {
                let delta = paths_at(region, self.at)?;
                let pairs = delta.intersect(&Predicate::qualified(rows, Predicate::True));
                let record: RecordDelivery =
                    Box::new(move |seen| seen.partners = seen.partners.union(&delta));
                (pairs, record)
            }
        })
    }
}

impl Pairing {
    /// Pass `restated` on. A complete region is passed on unmarked. Both inputs of a pairing read
    /// what one push brings in the same landing, so each pair's halves complete together. Halves
    /// pushed by different pipelines are joined by [`Delivered`]: the push that delivers a pair's
    /// second half announces the pair.
    fn pass_on(&self, restated: &Projection, landing: &mut Landing<'_>) {
        self.consumer.notify(restated, landing);
    }
}

impl Consumer for Pairing {
    /// Restates a region of one input as the pairs it reaches ([`Delivered`]), passed on as
    /// [`pass_on`](Self::pass_on) says.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        // A delivery grows what has been delivered and is cut by it: a landing that queues
        // packages, a breaker's push or a range's arrival ([`Landing::is_delivery`]). Any other
        // landing states what is decided rather than what arrived, so it is cut by nothing and
        // takes every pair it decides.
        let delivery = landing.is_delivery();
        // The pairs are read and the delta recorded under one lock, so of two deliveries on
        // different threads the later one announces each pair they complete, and once. The lock
        // is released before the region is passed on.
        let mut delivered = self
            .delivered
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        // A row side's values are no part of the pairs' values the pairing spells, so a part of a
        // row's values is restated through the whole row: a change names the row's pairs whole,
        // which names more than changed, and a complete part completes no pair.
        let whole_rows;
        let region = match (self.side, region.names_part_of_values()) {
            (PairingSide::Rows(_), true) => {
                whole_rows = region.rows();
                &whole_rows
            }
            _ => region,
        };
        // A region within some values, or a union with one: each arm's keys pair as keys do, and
        // the part of the values it names stands under each pair it announces. A part is new
        // information under every pair it reaches, so it is announced under every pair whose other
        // half has arrived, not only under the pairs its keys complete.
        if region.names_part_of_values() {
            let mut restated = Vec::new();
            for arm in region_arms(region) {
                let (keys_only, values) = match &arm {
                    // A selected collection's keys can be expressed relative to an enclosing
                    // group. At the paired level these name the pairs themselves.
                    Projection::Within { .. }
                        if matches!(self.side, PairingSide::Paths)
                            && let Some(paths) = paths_at(&arm, self.at) =>
                    {
                        (Projection::keys_at(self.at, paths), None)
                    }
                    Projection::Within {
                        level,
                        keys,
                        values,
                    } => (
                        Projection::keys_at(*level, keys.clone()),
                        Some((**values).clone()),
                    ),
                    whole => (whole.clone(), None),
                };
                // The pairs the arm's keys complete, cut by what the other side has delivered.
                let Some((completed, record)) = self.pairs(&keys_only, delivery, &delivered) else {
                    panic!("{arm:?} names keys beneath what a pairing restates");
                };
                let every = self.pairs(&keys_only, false, &delivered);
                let rows = match delivery {
                    true => delivered.rows.clone(),
                    false => crate::interpreter::Predicate::True,
                };
                if delivery {
                    record(&mut delivered);
                }
                let pairs = match (&values, every) {
                    (None, _) => Projection::keys_at(self.at, completed),
                    (Some(values), Some((all, _))) => {
                        let reached = match self.side {
                            PairingSide::ConstantKeys => {
                                all.intersect(&crate::interpreter::Predicate::qualified(
                                    rows,
                                    crate::interpreter::Predicate::True,
                                ))
                            }
                            PairingSide::Paths => {
                                all.intersect(&crate::interpreter::Predicate::qualified(
                                    rows,
                                    crate::interpreter::Predicate::True,
                                ))
                            }
                            PairingSide::Rows(_) => panic!(
                                "{arm:?}: a row side names its rows whole, not part of their values"
                            ),
                        };
                        Projection::within(self.at, reached, values.clone())
                    }
                    (Some(_), None) => unreachable!("read above"),
                };
                restated.push(pairs);
            }
            drop(delivered);
            let restated = Projection::any_of(restated);
            if landing.is_delivery() && restated == Projection::Nothing {
                return;
            }
            self.pass_on(&restated, landing);
            return;
        }
        // A region beneath a constant's outermost keys names paths inside the values of keys
        // that have already arrived, beneath every row: the same paths under each delivered row,
        // `level` levels further down, and its outermost keys as delivered.
        if let (PairingSide::ConstantKeys, Projection::Keys { level, keys }) = (self.side, region)
            && *level > CurryLevel::OUTERMOST
        {
            let rows = match delivery {
                true => delivered.rows.clone(),
                false => crate::interpreter::Predicate::True,
            };
            if delivery {
                let outermost = outermost_keys(keys, level.index());
                delivered.partners = delivered.partners.union(&outermost);
            }
            drop(delivered);
            let paths = crate::interpreter::tiling::beneath_keys(keys, &rows, level.index());
            let restated =
                Projection::keys_at(CurryLevel::new(self.at.index() + level.index()), paths);
            if landing.is_delivery() && restated == Projection::Nothing {
                return;
            }
            self.pass_on(&restated, landing);
            return;
        }
        let Some((pairs, record)) = self.pairs(region, delivery, &delivered) else {
            drop(delivered);
            match self.side {
                // A constant's region beneath its outermost keys names no key of the pairs.
                PairingSide::ConstantKeys => self.consumer.notify(&Projection::Everything, landing),
                _ => self.consumer.notify(region, landing),
            }
            return;
        };
        if delivery {
            record(&mut delivered);
        }
        drop(delivered);
        if landing.is_delivery() && pairs.is_false() {
            return;
        }
        let restated = Projection::keys_at(self.at, pairs);
        self.pass_on(&restated, landing);
    }
}
