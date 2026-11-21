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

/// Notify `shared` of `region`. A notification that reaches a shared consumer this thread is
/// already notifying calls [`Landing::reentered`] instead.
///
/// It takes no lock: a consumer guards its own state and releases it before it forwards a
/// notification. Two threads can notify one consumer at once.
pub(crate) fn notify_shared<C: Consumer + ?Sized>(
    shared: &Arc<C>,
    region: &Projection,
    landing: &mut Landing<'_>,
) {
    match Notifying::enter(shared) {
        Some(_notifying) => C::notify(shared, region, landing),
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

/// Preserve notifications above `level` when the value at that level changes shape.
/// Changes below it name their enclosing rows; completion passes only for whole values.
pub(crate) fn through_values(
    level: CurryLevel,
    output: &crate::interpreter::Tiling,
    downstream: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    if level == CurryLevel::OUTERMOST {
        return widening(downstream);
    }
    Box::new(ThroughValues {
        level,
        output: output.clone(),
        downstream,
    })
}

struct ThroughValues {
    level: CurryLevel,
    output: crate::interpreter::Tiling,
    downstream: Box<dyn Consumer>,
}

impl Consumer for ThroughValues {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let already_whole = *region == Projection::Everything;
        let region = if landing.is_complete() {
            // A complete part of some values completes no value this operator reshapes: only the
            // arms naming whole keys pass.
            let whole = Projection::any_of(
                region_arms(region)
                    .into_iter()
                    .filter(|arm| !matches!(arm, Projection::Within { .. })),
            );
            let guard = crate::interpreter::tiling::through_shared_levels(
                whole.collection_guard(),
                self.level.index(),
                &self.output,
            );
            Projection::of(&guard).expect("completed shared rows name output rows")
        } else {
            region.above(self.level)
        };
        if !landing.is_complete() && !already_whole && region == Projection::Everything {
            landing.widened(|landing| self.downstream.notify(&region, landing));
        } else {
            self.downstream.notify(&region, landing);
        }
    }
}

struct Widening(Box<dyn Consumer>);

impl Consumer for Widening {
    /// A change widens to every key. A complete region passes as every key where its source is
    /// wholly complete, and not at all otherwise: each output key depends on every input key, so
    /// the path completes only part of what a row depends on.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        landing.completing_part(|landing| match region {
            Projection::Everything => self.0.notify(region, landing),
            _ if landing.is_wholly_complete() => self.0.notify(&Projection::Everything, landing),
            _ if landing.is_complete() => {}
            _ => landing.widened(|landing| self.0.notify(&Projection::Everything, landing)),
        });
    }
}

/// [`restating`] for a lookup's collection operand: the rows a key of the operand names read that
/// key and also their input's value, so the complete region it passes names only part of what
/// those rows depend on ([`Landing::completing_part`]).
pub fn restating_lookup(
    restate: Box<dyn Fn(&Projection) -> Projection + Send + Sync>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(RestatingLookup(Restating(restate, consumer)))
}

struct RestatingLookup(Restating);

impl Consumer for RestatingLookup {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        landing.completing_part(|landing| self.0.notify(region, landing));
    }
}

/// `consumer` behind a consumer that passes each region on as `restate` names it, a change as a
/// complete region: an operator that keeps its input's keys under another spelling, as `Uncurry`
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

    /// [`notify`](Consumer::notify) inside the path's completes-part mark.
    fn pass_on(&self, region: &Projection, landing: &mut Landing<'_>) {
        if landing.is_complete() {
            match region {
                Projection::Keys { level, .. } if *level >= self.at => {
                    if landing.is_wholly_complete() {
                        self.consumer.notify(&Projection::Everything, landing);
                    }
                }
                standing => self.consumer.notify(standing, landing),
            }
            return;
        }
        match self.restated(region) {
            Some(restated) => self.consumer.notify(&restated, landing),
            None => {
                landing.widened(|landing| self.consumer.notify(&Projection::Everything, landing))
            }
        }
    }
}

impl Consumer for OneLevelIn {
    /// A complete region of the standing levels passes as it is. One that names keys at or beneath
    /// level `at` passes as every key where its source is wholly complete, and not at all
    /// otherwise: which output keys an input row stands beneath depends on its values, which no
    /// region carries, so the path completes only part of what a row depends on.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        landing.completing_part(|landing| self.pass_on(region, landing));
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

    #[test]
    fn a_replaced_whole_value_walks_a_widened_route() {
        use crate::interpreter::dispatcher::PipelineId;
        use crate::interpreter::{BaseType, Extent, Tiling};
        struct Entry;
        impl Consumer for Entry {
            fn notify(&self, _: &Projection, landing: &mut Landing<'_>) {
                landing.queue(
                    PipelineId(0),
                    &crate::interpreter::TileGuard::Scalar(crate::interpreter::Predicate::True),
                );
            }
        }
        let output = Tiling::Scalar(Extent::Base(BaseType::Int));
        let consumer = through_values(CurryLevel::OUTERMOST, &output, Box::new(Entry));
        let mut landing = Landing::route();
        consumer.notify(
            &Projection::admitting(crate::interpreter::Predicate::point(
                crate::interpreter::Value::UInt(0),
            )),
            &mut landing,
        );
        let reached = landing.routes();
        assert_eq!(reached.len(), 1);
        assert!(!reached[0].keeps_keys);
        assert!(reached[0].completes_part);
    }

    /// A value replaced beneath the outermost level widens a change only where it names keys of
    /// that level: a route walk of a path through it keeps the keys of a push of one outer key, and
    /// widens a push of an inner key beneath every outer one, as a group's row is pushed.
    #[test]
    fn a_replaced_inner_value_widens_only_a_push_beneath_its_level() {
        use crate::interpreter::dispatcher::PipelineId;
        use crate::interpreter::{BaseType, Extent, Predicate, TileGuard, Tiling, Value};
        struct Entry;
        impl Consumer for Entry {
            fn notify(&self, _: &Projection, landing: &mut Landing<'_>) {
                landing.queue(PipelineId(0), &TileGuard::Scalar(Predicate::True));
            }
        }
        let uint = || Extent::Base(BaseType::UInt);
        let output = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::Scalar(Extent::Base(BaseType::Int))),
        );
        let consumer = through_values(CurryLevel::new(1), &output, Box::new(Entry));
        let keeps = |region: Projection| {
            let mut landing = Landing::route();
            consumer.notify(&region, &mut landing);
            let routes = landing.routes();
            assert_eq!(routes.len(), 1, "{region:?}");
            routes[0].keeps_keys
        };
        assert!(keeps(Projection::of_path(&[Value::UInt(0)])));
        assert!(!keeps(Projection::keys_at(
            CurryLevel::new(1),
            Predicate::point(Value::UInt(0))
        )));
    }

    #[test]
    fn replaced_values_pass_changes_but_only_whole_value_completion() {
        use crate::interpreter::dispatcher::PipelineId;
        use crate::interpreter::{BaseType, Extent, Predicate, Tiling, Value};
        struct Received(Arc<RwLock<Vec<Projection>>>);
        impl Consumer for Received {
            fn notify(&self, region: &Projection, _: &mut Landing<'_>) {
                self.0
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(region.clone());
            }
        }
        let received = Arc::new(RwLock::new(Vec::new()));
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let consumer = through_values(
            CurryLevel::new(1),
            &tiling,
            Box::new(Received(received.clone())),
        );
        let row = Predicate::point(Value::UInt(4));
        let part = Projection::keys_at(
            CurryLevel::new(1),
            Predicate::qualified(row.clone(), Predicate::point(Value::UInt(7))),
        );
        consumer.notify(&part, &mut Landing::probe(PipelineId(0)));
        consumer.notify(&part, &mut Landing::probe_complete(PipelineId(0)));
        let whole = Projection::keys_at(
            CurryLevel::new(1),
            Predicate::qualified(row.clone(), Predicate::True),
        );
        consumer.notify(&whole, &mut Landing::probe_complete(PipelineId(0)));
        let outer = Projection::admitting(row);
        assert_eq!(
            *received.read().unwrap_or_else(PoisonError::into_inner),
            vec![outer.clone(), Projection::Nothing, outer]
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

/// [`Delivered`], shared by the consumers in front of one pairing operator's inputs.
pub(crate) type SharedDelivered = Arc<std::sync::Mutex<Delivered>>;

/// A [`Delivered`] with nothing delivered yet of a side whose keys arrive from a source, and
/// everything of a side that reads none, which holds all its keys from the start
/// ([`TileOperator::arrives_from_a_source`](crate::interpreter::tile_operators::TileOperator::arrives_from_a_source)).
pub(crate) fn nothing_delivered(rows_arrive: bool, partners_arrive: bool) -> SharedDelivered {
    let held = |arrive: bool| match arrive {
        true => crate::interpreter::Predicate::False,
        false => crate::interpreter::Predicate::True,
    };
    Arc::new(std::sync::Mutex::new(Delivered {
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
        if restated == Projection::Nothing && *region != Projection::Nothing && landing.queues() {
            return;
        }
        self.1.notify(&restated, landing);
    }
}

/// `consumer` behind a consumer that forwards a region of a record's field `name`, the record
/// standing at `level` beneath rows, as that field of the rows it reaches: the rows a region of the
/// field's keys runs through, within the field `name`'s part, and nothing of the other fields.
/// `Zip` passes this to each arm, whose rows are the pair's and whose values are one field of it,
/// so a push on one arm names no part of another arm's field.
pub fn field_beneath_rows(
    name: smol_str::SmolStr,
    level: CurryLevel,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    let rows = level
        .enclosing()
        .expect("a field beneath rows stands beneath a level of rows");
    Box::new(FieldBeneathRows {
        name,
        rows,
        consumer,
    })
}

struct FieldBeneathRows {
    name: smol_str::SmolStr,
    rows: CurryLevel,
    consumer: Box<dyn Consumer>,
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

impl FieldBeneathRows {
    /// The rows `restated`, a region of the rows, names this arm's field of whole: the arm's part
    /// of those rows.
    fn whole_field_rows(&self, restated: &Projection) -> Projection {
        Projection::any_of(region_arms(restated).into_iter().filter_map(|arm| {
            match arm {
                Projection::Within {
                    level,
                    keys,
                    values,
                } => (values.field(&self.name) == Projection::Everything)
                    .then(|| Projection::keys_at(level, keys)),
                whole => Some(whole),
            }
        }))
    }
}

impl Consumer for FieldBeneathRows {
    /// A notification names keys, and what of each row's value is final is stated in the tiles
    /// the row's reader pulls. A change of one field names the rows it runs through. A complete
    /// region names the rows whose field it completes whole, which says this arm's part of those
    /// rows is final; the reader joins it with the other inputs it reads.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let restated = self.restated(region);
        let rows = match landing.is_complete() {
            false => restated.rows(),
            true => self.whole_field_rows(&restated),
        };
        if rows == Projection::Nothing && landing.queues() {
            return;
        }
        self.consumer.notify(&rows, landing);
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
        match (region.names_part_of_values(), landing.is_complete()) {
            (false, _) => self.0.notify(region, landing),
            (true, false) => self.0.notify(&region.rows(), landing),
            // A complete part of the input's value completes none of the value computed from all
            // of it.
            (true, true) => self.0.notify(&whole_rows_of(region), landing),
        }
    }
}

/// The rows `region` names whole: its arms of keys, and of each arm within some values the keys
/// where the part it names is all of the values ([`Projection::Everything`]).
fn whole_rows_of(region: &Projection) -> Projection {
    Projection::any_of(region_arms(region).into_iter().filter_map(|arm| match arm {
        Projection::Within {
            level,
            keys,
            values,
        } => (*values == Projection::Everything).then(|| Projection::keys_at(level, keys)),
        whole => Some(whole),
    }))
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
/// keys beneath it. A region above `to` admits every path beneath its keys.
fn paths_at(region: &Projection, to: CurryLevel) -> Option<crate::interpreter::Predicate> {
    use crate::interpreter::Predicate;
    let (mut level, mut keys) = match region {
        Projection::Within { .. } | Projection::Or(_) => panic!(
            "this reading has no part of some values: a projection within values or an `Or` reaches it"
        ),
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
    ) -> Option<(
        crate::interpreter::Predicate,
        Box<dyn FnOnce(&mut Delivered)>,
    )> {
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
                let record: Box<dyn FnOnce(&mut Delivered)> =
                    Box::new(move |seen| seen.rows = seen.rows.union(&delta));
                (pairs, record)
            }
            PairingSide::ConstantKeys => {
                let delta = paths_at(region, CurryLevel::OUTERMOST)?;
                let pairs = Predicate::qualified(rows, delta.clone());
                let record: Box<dyn FnOnce(&mut Delivered)> =
                    Box::new(move |seen| seen.partners = seen.partners.union(&delta));
                (pairs, record)
            }
            PairingSide::Paths => {
                let delta = paths_at(region, self.at)?;
                let pairs = delta.intersect(&Predicate::qualified(rows, Predicate::True));
                let record: Box<dyn FnOnce(&mut Delivered)> =
                    Box::new(move |seen| seen.partners = seen.partners.union(&delta));
                (pairs, record)
            }
        })
    }
}

impl Pairing {
    /// Pass `restated` on. A change of one input names pairs whose other half may still change,
    /// so it completes part of what a pair depends on ([`Landing::completing_part`]). A complete
    /// region is passed on unmarked: both inputs of a pairing read what one push brings in the
    /// same landing, so each pair's halves complete together, and halves from different
    /// pipelines are joined by the reader's record per read.
    fn pass_on(&self, restated: &Projection, landing: &mut Landing<'_>) {
        match landing.is_complete() {
            true => self.consumer.notify(restated, landing),
            false => landing.completing_part(|landing| self.consumer.notify(restated, landing)),
        }
    }
}

impl Consumer for Pairing {
    /// Restates a region of one input as the pairs it reaches ([`Delivered`]), passed on as
    /// [`pass_on`](Self::pass_on) says.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        // A delivery grows what has been delivered and is cut by it: a landing that queues
        // packages, a breaker's push or a range's arrival ([`Landing::queues`]). Any other landing
        // states what is decided rather than what arrived, so it is cut by nothing and takes every
        // pair it decides.
        let delivery = landing.queues();
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
                whole_rows = match landing.is_complete() {
                    false => region.rows(),
                    true => Projection::any_of(
                        region_arms(region)
                            .into_iter()
                            .filter(|arm| !arm.names_part_of_values()),
                    ),
                };
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
                let Some((_, record)) = self.pairs(&keys_only, delivery, &delivered) else {
                    panic!("{arm:?} names keys beneath what a pairing restates");
                };
                let every = self.pairs(&keys_only, false, &delivered);
                let (rows, partners) = match delivery {
                    true => (delivered.rows.clone(), delivered.partners.clone()),
                    false => (
                        crate::interpreter::Predicate::True,
                        crate::interpreter::Predicate::True,
                    ),
                };
                if delivery {
                    record(&mut delivered);
                }
                let pairs = match (&values, every) {
                    (None, _) => {
                        let (pairs, _) = self
                            .pairs(&keys_only, false, &Delivered { rows, partners })
                            .expect("read above");
                        Projection::keys_at(self.at, pairs)
                    }
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
            if landing.queues() && restated == Projection::Nothing {
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
            if landing.queues() && restated == Projection::Nothing {
                return;
            }
            self.pass_on(&restated, landing);
            return;
        }
        let Some((pairs, record)) = self.pairs(region, delivery, &delivered) else {
            drop(delivered);
            match self.side {
                // A constant's region beneath its outermost keys names no key of the pairs.
                PairingSide::ConstantKeys => landing.completing_part(|landing| {
                    landing
                        .widened(|landing| self.consumer.notify(&Projection::Everything, landing))
                }),
                _ => self.consumer.notify(region, landing),
            }
            return;
        };
        if delivery {
            record(&mut delivered);
        }
        drop(delivered);
        if landing.queues() && pairs.is_false() {
            return;
        }
        let restated = Projection::keys_at(self.at, pairs);
        self.pass_on(&restated, landing);
    }
}
