use std::sync::PoisonError;
use std::sync::RwLock;
use std::{collections::HashMap, sync::Arc};

use crate::ccl::FieldKey;
use crate::interpreter::CurryLevel;
use crate::interpreter::{Consumer, DataSourceDomainExtentImpl, Projection, dispatcher::Landing};

// Construction and notification delivery share one gate; recursive calls on its owner reuse it.
#[derive(Default)]
struct ControlThread {
    lock: Option<std::sync::MutexGuard<'static, ()>>,
    depth: usize,
    active: std::collections::HashSet<usize>,
}
thread_local! {
    static CONTROL_THREAD: std::cell::RefCell<ControlThread> = Default::default();
}

pub(crate) struct ControlGuard(std::marker::PhantomData<std::sync::MutexGuard<'static, ()>>);

pub(crate) fn control_plane() -> ControlGuard {
    static CONTROL: std::sync::Mutex<()> = std::sync::Mutex::new(());
    CONTROL_THREAD.with(|thread| {
        let mut thread = thread.borrow_mut();
        if thread.depth == 0 {
            thread.lock = Some(CONTROL.lock().unwrap_or_else(PoisonError::into_inner));
        }
        thread.depth += 1;
    });
    ControlGuard(std::marker::PhantomData)
}

impl Drop for ControlGuard {
    fn drop(&mut self) {
        CONTROL_THREAD.with(|thread| {
            let mut thread = thread.borrow_mut();
            thread.depth -= 1;
            if thread.depth == 0 {
                drop(thread.lock.take());
            }
        });
    }
}

fn with_consumer<C: Consumer + ?Sized>(shared: &Arc<RwLock<C>>, f: impl FnOnce(&mut C)) -> bool {
    let _control = control_plane();
    let identity = Arc::as_ptr(shared) as *const () as usize;
    if !CONTROL_THREAD.with(|thread| thread.borrow_mut().active.insert(identity)) {
        return false;
    }
    struct Active(usize);
    impl Drop for Active {
        fn drop(&mut self) {
            CONTROL_THREAD.with(|thread| {
                thread.borrow_mut().active.remove(&self.0);
            });
        }
    }
    let _active = Active(identity);
    f(&mut *shared.write().unwrap_or_else(PoisonError::into_inner));
    true
}

pub(crate) fn notify_shared<C: Consumer + ?Sized>(
    shared: &Arc<RwLock<C>>,
    region: &Projection,
    landing: &mut Landing<'_>,
) {
    if !with_consumer(shared, |consumer| consumer.notify(region, landing)) {
        landing.reentered();
    }
}

/// A consumer handle shared by notification forwarders.
/// It carries notifications, not tile data.
pub type SharedConsumer = Arc<RwLock<dyn Consumer>>;

/// Share a consumer between its input paths. Pipeline entries end notification propagation.
pub fn shared_consumer(consumer: Box<dyn Consumer>) -> SharedConsumer {
    Arc::new(RwLock::new(consumer))
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        let already_whole = *region == Projection::Everything;
        let region = if landing.is_complete() {
            let guard = crate::interpreter::tiling::through_shared_levels(
                region.collection_guard(),
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        landing.completing_part(|landing| match region {
            Projection::Everything => self.0.notify(region, landing),
            _ if landing.is_wholly_complete() => self.0.notify(&Projection::Everything, landing),
            _ if landing.is_complete() => {}
            _ => landing.widened(|landing| self.0.notify(&Projection::Everything, landing)),
        });
    }
}

/// `consumer` behind a consumer that widens like [`widening`] except for a complete region, which it
/// passes as `restate` names it: the region of the operator's keys each of whose values the input
/// region decides. An operator that re-keys its input knows which of its keys an input key
/// contributes to, as `Uncurry` pairs an outer key with each inner key beneath it, so a complete
/// region of its input decides that region of its own keys, which [`widening`] would hold back
/// until the input is wholly complete.
pub fn widening_restating_complete(
    restate: fn(&Projection) -> Projection,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(WideningRestatingComplete(restate, consumer))
}

struct WideningRestatingComplete(fn(&Projection) -> Projection, Box<dyn Consumer>);

impl Consumer for WideningRestatingComplete {
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        match region {
            Projection::Everything => self.1.notify(region, landing),
            _ if landing.is_complete() => self.1.notify(&(self.0)(region), landing),
            _ => landing.widened(|landing| self.1.notify(&Projection::Everything, landing)),
        }
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        landing.completing_part(|landing| self.0.notify(region, landing));
    }
}

/// `consumer` behind a consumer that passes each region on as `restate` names it, a change as a
/// complete region: an operator that keeps its input's keys under another spelling, as `Uncurry`
/// beneath a standing level names an outer and an inner key as one pair, restates both exactly.
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        self.1.notify(&(self.0)(region), landing);
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
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
    fn pass_on(&mut self, region: &Projection, landing: &mut Landing<'_>) {
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
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
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
            fn notify(&mut self, _: &Projection, landing: &mut Landing<'_>) {
                landing.queue(
                    PipelineId(0),
                    &crate::interpreter::TileGuard::Scalar(crate::interpreter::Predicate::True),
                );
            }
        }
        let output = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut consumer = through_values(CurryLevel::OUTERMOST, &output, Box::new(Entry));
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
            fn notify(&mut self, _: &Projection, landing: &mut Landing<'_>) {
                landing.queue(PipelineId(0), &TileGuard::Scalar(Predicate::True));
            }
        }
        let uint = || Extent::Base(BaseType::UInt);
        let output = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::Scalar(Extent::Base(BaseType::Int))),
        );
        let mut consumer = through_values(CurryLevel::new(1), &output, Box::new(Entry));
        let keeps = |region: Projection, consumer: &mut Box<dyn Consumer>| {
            let mut landing = Landing::route();
            consumer.notify(&region, &mut landing);
            let routes = landing.routes();
            assert_eq!(routes.len(), 1, "{region:?}");
            routes[0].keeps_keys
        };
        assert!(keeps(Projection::of_path(&[Value::UInt(0)]), &mut consumer));
        assert!(!keeps(
            Projection::keys_at(CurryLevel::new(1), Predicate::point(Value::UInt(0))),
            &mut consumer
        ));
    }

    #[test]
    fn replaced_values_pass_changes_but_only_whole_value_completion() {
        use crate::interpreter::dispatcher::PipelineId;
        use crate::interpreter::{BaseType, Extent, Predicate, Tiling, Value};
        struct Received(Arc<RwLock<Vec<Projection>>>);
        impl Consumer for Received {
            fn notify(&mut self, region: &Projection, _: &mut Landing<'_>) {
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
        let mut consumer = through_values(
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
            &mut *forwarding_consumer_keeping_keys(&shared),
            &keys,
        );
        crate::interpreter::dispatcher::notify_for_test(&mut *forwarding_consumer(&shared), &keys);
        assert_eq!(
            *received.read().unwrap_or_else(PoisonError::into_inner),
            [keys, Projection::Everything]
        );
    }
}
