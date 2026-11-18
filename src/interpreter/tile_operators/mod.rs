//! Tile operator and producer types for the CCL dataflow graph.
//!
//! A [`TileOperator`] is a static descriptor of a computation node — it knows
//! its output [`Tiling`] and can create a live [`TileProducer`] via
//! [`TileOperator::subscribe`].  A [`TileProducer`] is the runtime counterpart:
//! it can answer `get` queries and accept `release` notifications.
//!
//! Operators and producers mirror each other: `FooOperator` / `FooProducer`
//! pairs appear throughout the module.
//!
//! The operators are grouped into submodules by cohesive operator+producer
//! cluster; this `mod.rs` carries the shared spine (the [`TileOperator`] /
//! [`TileProducer`] traits, `OperatorBase` and [`ProducerBase`] with their
//! `impl_*_base` macros, and [`TilePathStep`]) and re-exports every cluster so
//! consumers continue to reach items as `tile_operators::X`.

#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
use smol_str::SmolStr;
use std::sync::PoisonError;
use std::sync::RwLock;
use std::{
    collections::HashMap,
    sync::Arc,
    sync::{Mutex, OnceLock},
};

use log::trace;

use crate::interpreter::DataSourceDomainExtentImpl;
use crate::interpreter::dispatcher::Pushes;
use crate::interpreter::tiling::Restates;
pub use crate::interpreter::tiling::{
    CurryLevel, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
};
use crate::{
    ccl::provenance::NodeId,
    interpreter::operator_graph::{EdgeKind, InputEdgeSpec},
    interpreter::value_probe::ProbeSlot,
    interpreter::{
        ColumnValue, Consumer, Extent, Projection, SharedConsumer, SubscribeContext, Value,
        forwarding_consumer, forwarding_consumer_keeping_keys, validate_tile, widening,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

mod aggregate;
mod breaker_reader;
pub(crate) use breaker_reader::share_breaker;
mod combinators;
mod cycle_slot;
#[cfg(test)]
mod dispatcher_tests;
#[cfg(test)]
mod dispatcher_thread_tests;
mod extract_final;
mod fan;
pub(crate) mod fanout;
#[cfg(test)]
mod forwarding_tests;
mod group_aggregate;
#[cfg(test)]
mod growing;
mod helpers;
mod iterate;
mod lookup;
mod map;
#[cfg(test)]
mod program_run_tests;
mod reading;
mod rekey_sorted;
mod reshape;
mod scalar;
mod sink_breaker;
#[cfg(test)]
mod store_breaker_tests;
mod union;

pub use aggregate::*;
pub use combinators::*;
pub use cycle_slot::*;
pub use extract_final::*;
pub use fan::*;
pub use fanout::*;
pub(crate) use group_aggregate::GroupAggregate;
pub use helpers::*;
pub use iterate::*;
pub use lookup::*;
pub use map::*;
pub use reading::*;
pub use rekey_sorted::*;
pub use reshape::*;
pub use scalar::*;
pub(crate) use sink_breaker::SinkBreaker;
pub use union::*;

/// Static descriptor of a computation node in the tile dataflow graph.
///
/// An operator knows its output [`Tiling`] and can instantiate a live
/// [`TileProducer`] by subscribing a [`Consumer`].  Operators are
/// constructed at compile time; producers are created on demand at runtime.
pub trait TileOperator: Send + Sync {
    /// Get the extent (type) of this operator.
    fn extent(&self) -> Extent {
        self.tiling().extent()
    }

    /// Return the [`Tiling`] that describes this operator's output shape.
    /// If the operator has unbound arguments, the tiling will be a curried function
    /// from inputs to the output.
    fn tiling(&self) -> &Tiling;

    /// This operator's identity, or `None` for a type that carries no
    /// `OperatorBase`.
    ///
    /// Production operators supply this through [`impl_operator_base`]. The
    /// default exists for test doubles, which need no identity: nothing folds
    /// them into a provenance table and nothing renders them in a pane.
    fn operator_id(&self) -> Option<NodeId> {
        None
    }

    /// State this operator's inputs to `visit`, in the order the graph holds
    /// them.
    ///
    /// The single statement of what an operator holds. The graph walk builds the
    /// operator pane from it, so an input stated nowhere is an edge the pane
    /// does not have and a subtree the pane may lose entirely.
    ///
    /// A visitor rather than a returned list because two inputs are reached
    /// through an `RwLock`: the read lives for the call and cannot outlive
    /// it. Required rather than defaulted so that a new operator states its
    /// inputs or fails to compile.
    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>));

    /// The concrete type's short name, e.g. `"MapResult"`.
    ///
    /// Split out of [`inspect`](Self::inspect) so a caller that wants only the
    /// name pays for the name: `inspect` recurses into upstream operators, so
    /// reading a label off it is quadratic in the depth of the graph.
    fn kind(&self) -> &'static str {
        short_type_name::<Self>()
    }

    fn subscribe(
        self: Arc<Self>,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer>;

    /// Render this operator and what it holds as an [`InspectNode`].
    ///
    /// The children are [`visit_inputs`](Self::visit_inputs)' `Value` edges, so
    /// an operator states what it holds once and this reads the same answer the
    /// graph walk does. `Share` edges are left out: a fan slot's edge to its
    /// fan input would draw the shared subtree once per branch, and following
    /// only `Value` edges is what makes this terminate without a cycle guard —
    /// they are acyclic, which `assert_graph_invariants` pins.
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new(self.kind()).with_tiling(self.tiling().to_string());
        if let Some(annotation) = self.inspect_annotation() {
            node = node.annotate(annotation);
        }
        let mut children = Vec::new();
        self.visit_inputs(&mut |spec| {
            if let EdgeKind::Value { .. } = spec.kind {
                children.push((spec.role.to_string(), spec.target.inspect(opts)));
            }
        });
        children
            .into_iter()
            .fold(node, |n, (role, child)| n.child(role, child))
    }

    /// An extra label beyond this operator's kind and tiling — a constant's
    /// value, a variant arm's tag. What it holds is not this: that is
    /// [`visit_inputs`](Self::visit_inputs).
    fn inspect_annotation(&self) -> Option<String> {
        None
    }

    /// If Some, represents an equality constraint between all or part of the domain
    /// and the result (i.e. the deepest codomain) of the output of this operator.
    /// Individual operators should override this when they are able to automatically detect this constraint.
    /// For example, [`IterateExtent`] always produces an identity function output, so it returns `Some([])`.
    /// Other operators like [`FanOut`] and [`Memo`] preserve structure, so they pass the value through from their
    /// input
    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        None
    }
}

/// Per-display-name instance counters, shared across all producer types.
///
/// Each key is the display name of a producer (e.g. `"MapApply"`, `"Memo"`),
/// and the value is the next ID to assign.  IDs start at 1.
// shared-state-ok: an ID allocator. What crosses it is a name, never a value: no
// operator reads anything another operator computed, so the producer graph still
// describes the whole dataflow.
static PRODUCER_COUNTERS: OnceLock<Mutex<HashMap<&'static str, usize>>> = OnceLock::new();

/// Subscribe `op` at its universal guard with a consumer that forwards to `shared`, the
/// consumer every input of one operator wakes
/// ([`shared_consumer`](crate::interpreter::shared_consumer)).
pub(crate) fn subscribe_forwarding(
    op: &Arc<dyn TileOperator>,
    shared: &SharedConsumer,
    cx: &mut SubscribeContext,
) -> Box<dyn TileProducer> {
    op.clone().subscribe(
        op.tiling().universal_guard(),
        forwarding_consumer(shared),
        cx,
    )
}

/// The consumer an operator passes an input: `consumer` itself where the operator's outermost keys
/// are the input's, so that the input's region reaches the operator's consumer as it is, and a
/// widening consumer where the operator re-keys or reads the input whole. The rule is the
/// operator's row of the projection table (`src/interpreter/design-operators.md`, "Projection
/// guards"): an input is kept iff the row pulls it at the projection.
pub(crate) fn consumer_keeping_keys_if(
    keeps_keys: bool,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    match keeps_keys {
        true => consumer,
        false => widening(consumer),
    }
}

/// [`subscribe_forwarding`] for an input whose outermost keys are the operator's: the input's
/// region reaches the operator's consumer as it is.
pub(crate) fn subscribe_forwarding_keeping_keys(
    op: &Arc<dyn TileOperator>,
    shared: &SharedConsumer,
    cx: &mut SubscribeContext,
) -> Box<dyn TileProducer> {
    op.clone().subscribe(
        op.tiling().universal_guard(),
        forwarding_consumer_keeping_keys(shared),
        cx,
    )
}

/// [`subscribe_forwarding_keeping_keys`] where `keeps_keys`, and [`subscribe_forwarding`] where not.
pub(crate) fn subscribe_forwarding_keeping_keys_if(
    keeps_keys: bool,
    op: &Arc<dyn TileOperator>,
    shared: &SharedConsumer,
    cx: &mut SubscribeContext,
) -> Box<dyn TileProducer> {
    match keeps_keys {
        true => subscribe_forwarding_keeping_keys(op, shared, cx),
        false => subscribe_forwarding(op, shared, cx),
    }
}

/// What a pipeline breaker's operator passes its input, and what the breaker keeps. The breaker
/// keeps the consumer it was subscribed with, shared so the breaker can push to it. The consumer
/// is shared with notification forwarders. A placed input queues work for its breaker; an
/// unplaced input forwards news to caches inside the enclosing scheduled pipeline.
pub(crate) struct BreakerInput {
    /// The consumer to subscribe the input with.
    pub(crate) consumer: Box<dyn Consumer>,
    /// The breaker's own consumer, shared, which it pushes to (`ProducerBase::breaking`).
    pub(crate) downstream: SharedConsumer,
    /// The pipeline the entry queues for (`ProducerBase::breaking`).
    pub(crate) placement: crate::interpreter::dispatcher::Placement,
}

impl BreakerInput {
    /// The input consumer of a breaker subscribed with `consumer`, whose input answers `input`,
    /// and which keeps its input's keys where `keeps_keys`.
    pub(crate) fn new(consumer: Box<dyn Consumer>, input: &Tiling, keeps_keys: bool) -> Self {
        let shared = crate::interpreter::shared_consumer(consumer);
        let (entry, placement) = crate::interpreter::dispatcher::Entry::unplaced(input.clone());
        BreakerInput {
            consumer: Box::new(entry.inline_through(if keeps_keys {
                forwarding_consumer_keeping_keys(&shared)
            } else {
                forwarding_consumer(&shared)
            })),
            downstream: shared.clone(),
            placement,
        }
    }
}

/// The concrete type's name with its module path stripped, e.g. `"MapResult"`.
///
/// Every caller wants the same name and each had its own copy:
/// [`TileOperator::kind`], [`TileProducer::name`], [`TileProducer::alloc_id`]'s
/// counter key, and the label `OperatorBase::new` records.
pub(crate) fn short_type_name<T: ?Sized>() -> &'static str {
    let full = std::any::type_name::<T>();
    debug_assert!(
        !full.contains('<'),
        "short_type_name splits on the last `::`, which for a generic type falls \
         inside the generic argument list and returns a fragment of it: {full}"
    );
    full.rsplit_once("::").map_or(full, |(_, tail)| tail)
}

/// Common identity and tiling state shared by every [`TileOperator`].
///
/// The operator-side counterpart of [`ProducerBase`], and it exists for the same
/// reason: every operator held a `tiling` field and a trivial accessor for it.
/// Identity rides here too, because construction is the only point every
/// operator type passes through — there is no shared constructor, so a
/// [`NodeId`] taken anywhere else would be a call site's responsibility to
/// remember.
///
/// The id is drawn from the same counter as an expression node's. Conversion
/// runs after every rewrite phase and mints no expression nodes, so every
/// operator id is greater than every expression id in the same compile, and the
/// two sets are disjoint. `src/ccl/design/provenance.md` owns why that matters.
pub(crate) struct OperatorBase {
    /// Identity, minted at construction. See the type's own docs for why here.
    pub(crate) id: NodeId,
    /// Output tiling for this operator.
    pub(crate) tiling: Tiling,
}

impl OperatorBase {
    /// Mint an identity for an operator and row it against the expression the
    /// ambient conversion recording names.
    ///
    /// Construction is the minting point because it is the only place every
    /// operator type passes through: there is no shared constructor, so every
    /// operator is built at its own call site.
    ///
    /// What the operator holds is not stated here. It is read off the built
    /// operator by [`TileOperator::visit_inputs`], so the two cannot disagree.
    pub(crate) fn new(tiling: Tiling) -> Self {
        let id = NodeId::fresh();
        crate::ccl::provenance::on_mint(id);
        Self { id, tiling }
    }
}

/// Implement [`TileOperator::tiling`] and [`TileOperator::operator_id`] for a
/// concrete operator that stores its shared state in a field named `base`.
///
/// Usage: place `impl_operator_base!();` inside the `impl TileOperator for Foo`
/// block in place of the boilerplate accessors.
macro_rules! impl_operator_base {
    () => {
        fn tiling(&self) -> &Tiling {
            &self.base.tiling
        }
        fn operator_id(&self) -> Option<$crate::ccl::provenance::NodeId> {
            Some(self.base.id)
        }
    };
}
// Re-exported within the crate so the cluster submodules can pull it in with
// `use super::impl_operator_base;`, avoiding a `#[macro_export]` that would leak
// it to the crate root.
pub(crate) use impl_operator_base;

/// The regions an input has notified since they were last taken.
///
/// `subscribe` installs [`Self::consumer`] on the input before the producer exists;
/// `Arc<RwLock<_>>` connects the two and carries no tile values.
#[derive(Clone)]
pub struct Arrivals(
    // shared-state-ok: see the type doc.
    Arc<RwLock<Projection>>,
);

impl Arrivals {
    /// No region arrived yet.
    pub(crate) fn new() -> Self {
        Self(Arc::new(RwLock::new(Projection::Nothing)))
    }

    /// The union of the regions that arrived since the last call, which resets it.
    pub fn take(&self) -> Projection {
        std::mem::replace(
            &mut *self.0.write().unwrap_or_else(PoisonError::into_inner),
            Projection::Nothing,
        )
    }

    /// Whether a region has arrived since the last [`take`](Self::take), which it leaves
    /// recorded.
    pub fn pending(&self) -> bool {
        *self.0.read().unwrap_or_else(PoisonError::into_inner) != Projection::Nothing
    }

    /// Record that `arrived` has arrived.
    pub(crate) fn record(&self, arrived: &Projection) {
        let mut held = self.0.write().unwrap_or_else(PoisonError::into_inner);
        *held = held.union(arrived);
    }

    /// An input consumer that records the region before forwarding it downstream.
    pub fn consumer(&self, downstream: Box<dyn Consumer>) -> Box<dyn Consumer> {
        Box::new(RecordingConsumer {
            arrivals: self.clone(),
            downstream,
        })
    }
}

/// What [`Arrivals::consumer`] returns: records the region, then forwards it unchanged.
struct RecordingConsumer {
    arrivals: Arrivals,
    downstream: Box<dyn Consumer>,
}

impl Consumer for RecordingConsumer {
    /// Delivered notifications record the region; planning probes leave it unchanged.
    fn notify(
        &mut self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        if landing.is_delivery() {
            self.arrivals.record(region);
        }
        self.downstream.notify(region, landing);
    }
}

/// One collection level of a tile, keyed in [`completion_view`]'s map by the record fields
/// walked through to reach it and its collection depth. `complete` is the
/// region of paths reaching this level the tile calls complete — its own statement, and
/// the one above read a level further in, since a complete key is complete beneath.
/// `absent` is the paths the level records absent in every region (`absent_keys`), kept apart
/// from `complete` because an answer may leave it out.
struct CompletionNode {
    complete: Predicate,
    absent: Predicate,
}

/// One key or value of a tile, at the path that reaches it, so two outputs compare entry by
/// entry. `complete` says whether the tile calls that path complete.
struct Entry {
    value: EntryValue,
    complete: bool,
}

/// What sits at an entry's path: a key, a value, or what a store or an aggregation answers
/// for one row. Compared by equality rather than by its `Debug` rendering, which prints a
/// record's fields in hash order and so differs between equal values.
#[derive(Debug, PartialEq)]
enum EntryValue {
    Key,
    Value(Option<Value>),
    Frontier(Option<crate::interpreter::Position>),
    Row(Tile),
}

type NodeKey = (Vec<SmolStr>, usize);
type EntryKey = (Vec<SmolStr>, Vec<Value>);

/// Flatten `tile` into its collection levels and the entries it holds.
fn completion_view(tile: &Tile) -> (HashMap<NodeKey, CompletionNode>, HashMap<EntryKey, Entry>) {
    fn walk(
        tile: &Tile,
        label: &[SmolStr],
        level: usize,
        rows: &[Option<Vec<Value>>],
        above: &Predicate,
        nodes: &mut HashMap<NodeKey, CompletionNode>,
        entries: &mut HashMap<EntryKey, Entry>,
    ) {
        match tile {
            Tile::DataFunction {
                row_starts,
                domain,
                codomain,
                domain_predicate,
                deleted,
                absent_keys,
            } => {
                // The rule `Tile::completion_at` states, without `absent_keys`, which `absent`
                // holds.
                let complete = match level {
                    0 => domain_predicate.clone(),
                    _ => above.descend(1).union(domain_predicate),
                };
                let starts = row_starts;
                let mut keys: Vec<Option<Vec<Value>>> = vec![None; domain.len()];
                for (row, path) in rows.iter().enumerate() {
                    let from = starts.get(row).copied().unwrap_or(domain.len());
                    let to = starts.get(row + 1).copied().unwrap_or(domain.len());
                    let Some(path) = path else { continue };
                    for (key, slot) in keys.iter_mut().enumerate().take(to).skip(from) {
                        if deleted.contains(key) {
                            continue;
                        }
                        let mut at = path.clone();
                        at.push(domain.index_at(key));
                        entries.insert(
                            (label.to_vec(), at.clone()),
                            Entry {
                                value: EntryValue::Key,
                                complete: complete.contains_path(&at),
                            },
                        );
                        *slot = Some(at);
                    }
                }
                walk(codomain, label, level + 1, &keys, &complete, nodes, entries);
                nodes.insert(
                    (label.to_vec(), level),
                    CompletionNode {
                        complete,
                        absent: absent_keys.clone(),
                    },
                );
            }
            Tile::Record { fields, .. } => {
                for (field, field_tile) in fields {
                    let mut label = label.to_vec();
                    label.push(field.clone());
                    walk(field_tile, &label, level, rows, above, nodes, entries);
                }
            }
            Tile::Scalar(column) => {
                for (row, path) in rows.iter().enumerate() {
                    let Some(path) = path else { continue };
                    if row >= column.len() {
                        continue;
                    }
                    entries.insert(
                        (label.to_vec(), path.clone()),
                        Entry {
                            value: EntryValue::Value(Some(column.index_at(row))),
                            // A value at the root is the whole answer once it has arrived:
                            // a scalar holds no more than one.
                            complete: match level {
                                0 => true,
                                _ => above.contains_path(path),
                            },
                        },
                    );
                }
            }
            // A store's row is what it answers: its frontier, each key's seed, and each
            // key's value at every position it has decided. Its changelog is only how it
            // answers — reclaiming a released prefix keeps every carry source a live
            // position folds to, so the answers outside what was released do not move.
            Tile::Store {
                state,
                decided,
                frontier,
                ..
            } => {
                use crate::interpreter::commit_operator::{
                    store_decided_positions, store_frontier, store_seed_value, store_value_at,
                };
                use crate::interpreter::operator_conversion::store_key;
                let part = |name: &str| {
                    let mut l = label.to_vec();
                    l.push(SmolStr::new(name));
                    l
                };
                for (row, path) in rows.iter().enumerate() {
                    let Some(path) = path else { continue };
                    let one = tile.select_rows(&[row]);
                    // A store's seed is fixed for its whole life and a decided position's
                    // value never changes, so both are final wherever the store stands; its
                    // frontier only moves forward, which `completeness_violation`
                    // checks on its own.
                    let complete = true;
                    let entry = |value: EntryValue| Entry { value, complete };
                    entries.insert(
                        (part("frontier"), path.clone()),
                        Entry {
                            value: EntryValue::Frontier(store_frontier(&one)),
                            complete: false,
                        },
                    );
                    let Tile::Store {
                        decided: row_decided,
                        ..
                    } = &one
                    else {
                        unreachable!("a store's rows are stores")
                    };
                    let positions = store_decided_positions(row_decided, 0);
                    let names: Vec<SmolStr> = one.store_keys().cloned().collect();
                    for name in names {
                        let key = store_key(&crate::ccl::Label::from_runtime_key(&name));
                        // A store waiting for its seed has none yet; once it has one it
                        // keeps it.
                        let seed = store_seed_value(&one, &key);
                        entries.insert(
                            (part(&format!("seed.{name}")), path.clone()),
                            Entry {
                                complete: seed.is_some(),
                                value: EntryValue::Value(seed),
                            },
                        );
                        for position in &positions {
                            let mut at = path.clone();
                            at.push(position.value().clone());
                            entries.insert(
                                (part(&name), at),
                                entry(EntryValue::Value(store_value_at(&one, position, &key))),
                            );
                        }
                    }
                }
                // Each part of a store is also a collection over the store's rows, with a
                // statement of its own, and that statement is held to the contract like any
                // other collection's. A release of the store names its positions, which are
                // each part's keys, so a reclaimed prefix leaves every part as released.
                let Tile::Record { fields: logs, .. } = &**state else {
                    unreachable!("a store's state is a record of per-key changelogs")
                };
                for (name, log) in logs {
                    let label = part(&format!("#changelog.{name}"));
                    walk(log, &label, level, rows, above, nodes, entries);
                }
                walk(
                    decided,
                    &part("#decided"),
                    level,
                    rows,
                    above,
                    nodes,
                    entries,
                );
                walk(
                    frontier,
                    &part("#frontier"),
                    level,
                    rows,
                    above,
                    nodes,
                    entries,
                );
            }
            // An aggregation is one accumulator per row, compared row by row. Beneath no
            // level nothing is complete, and a row it has not reached holds nothing yet.
            other if level > 0 => {
                for (row, path) in rows.iter().enumerate().take(other.rows()) {
                    let Some(path) = path else { continue };
                    entries.insert(
                        (label.to_vec(), path.clone()),
                        Entry {
                            value: EntryValue::Row(other.select_rows(&[row])),
                            complete: above.contains_path(path),
                        },
                    );
                }
            }
            _ => {}
        }
    }
    let (mut nodes, mut entries) = (HashMap::new(), HashMap::new());
    walk(
        tile,
        &[],
        0,
        &[Some(Vec::new())],
        &Predicate::False,
        &mut nodes,
        &mut entries,
    );
    (nodes, entries)
}

/// Whether `guard` releases the root value under record fields `label` whole.
fn released_whole(guard: &TileGuard, label: &[SmolStr]) -> bool {
    match guard {
        g if g.is_universal() => true,
        TileGuard::Or(arms) => arms.iter().any(|arm| released_whole(arm, label)),
        TileGuard::Record(fields) => label
            .split_first()
            .and_then(|(field, rest)| fields.get(field).map(|g| released_whole(g, rest)))
            .unwrap_or(false),
        _ => false,
    }
}

/// The paths reaching collection level `level` under record fields `label` that `guard`
/// releases: a domain guard `d` codomain steps in names keys of level `d` and everything
/// beneath them.
fn released_at(guard: &TileGuard, label: &[SmolStr], level: usize) -> Predicate {
    fn walk(guard: &TileGuard, label: &[SmolStr], depth: usize, level: usize) -> Predicate {
        match guard {
            TileGuard::Or(arms) => arms
                .iter()
                .map(|arm| walk(arm, label, depth, level))
                .fold(Predicate::False, |all, one| all.union(&one)),
            TileGuard::Record(fields) => match label.split_first() {
                Some((field, rest)) => fields
                    .get(field)
                    .map_or(Predicate::False, |g| walk(g, rest, depth, level)),
                None => Predicate::False,
            },
            TileGuard::Function(FunctionGuard::Codomain(inner)) if depth < level => {
                walk(inner, label, depth + 1, level)
            }
            // The values of the level itself: a record field's cell, named at the rows its
            // leaf admits.
            TileGuard::Function(FunctionGuard::Codomain(inner)) if depth == level => {
                released_cells_at(inner, label)
            }
            TileGuard::Function(FunctionGuard::Domain(pred)) if depth <= level => {
                pred.descend(level - depth)
            }
            _ => Predicate::False,
        }
    }
    walk(guard, label, 0, level)
}

/// The paths whose value under record fields `label` `guard` names: a keyless leaf's rows.
fn released_cells_at(guard: &TileGuard, label: &[SmolStr]) -> Predicate {
    match guard {
        TileGuard::Or(arms) => arms
            .iter()
            .map(|arm| released_cells_at(arm, label))
            .fold(Predicate::False, |all, one| all.union(&one)),
        TileGuard::Record(fields) => match label.split_first() {
            Some((field, rest)) => fields
                .get(field)
                .map_or(Predicate::False, |g| released_cells_at(g, rest)),
            None => Predicate::False,
        },
        TileGuard::Scalar(pred) | TileGuard::Aggregation(pred) if label.is_empty() => {
            TileGuard::leaf_rows(pred).clone()
        }
        _ => Predicate::False,
    }
}

/// How `result` changes something `last` called complete, apart from removing what
/// `released` has released since: the two rules of `src/interpreter/design-operators.md`,
/// "The completeness contract". `None` where it changes nothing. A key at a path `last` recorded
/// absent breaks it too, released or not: the record holds in every region, and an answer that
/// leaves the record out withdraws nothing.
///
/// A statement covers every path at its level, including paths under rows that have not
/// arrived, so the second rule applies to them too: a key appearing under a row called
/// complete before it arrived breaks it.
fn completeness_violation(
    name: &str,
    last: &Tile,
    result: &Tile,
    released: &TileGuard,
) -> Option<String> {
    let (last_nodes, last_entries) = completion_view(last);
    let (result_nodes, result_entries) = completion_view(result);
    for ((label, level), node) in &last_nodes {
        let released_here = released_at(released, label, *level);
        let promised = node.complete.minus(&released_here);
        let kept = result_nodes
            .get(&(label.clone(), *level))
            .map_or(Predicate::False, |n| n.complete.clone());
        if !kept.subsumes(&promised) {
            return Some(format!(
                "{name} withdrew completion at level {level} of {label:?}: it called \
                 {promised:?} complete, and now calls only {kept:?} complete"
            ));
        }
    }
    // A root value is released by a release naming it whole, through the record fields that
    // reach it; a path beneath the root by one naming it.
    let is_released = |label: &Vec<SmolStr>, path: &Vec<Value>| match path.len() {
        0 => released_whole(released, label),
        n => released_at(released, label, n - 1).contains_path(path),
    };
    // A release lets a region leave the output, and nothing more: what a producer still
    // holds beneath a complete path, or adds beneath one, is checked whether or not a
    // consumer has since released it. Exempting those would hide exactly the broken
    // promise a consumer releases on.
    for ((label, path), entry) in &last_entries {
        if !entry.complete {
            continue;
        }
        match result_entries.get(&(label.clone(), path.clone())) {
            Some(now) if now.value == entry.value => {}
            None if is_released(label, path) => {}
            now => {
                return Some(format!(
                    "{name} changed {label:?} at {path:?}, which it had called complete: {:?} \
                     then {:?}, in {last:?} then {result:?}, having released {released:?}",
                    entry.value,
                    now.map(|n| &n.value)
                ));
            }
        }
    }
    // A store's frontier only moves forward: a position it has decided stays decided.
    for (key, entry) in &last_entries {
        let (
            EntryValue::Frontier(Some(then)),
            Some(Entry {
                value: EntryValue::Frontier(now),
                ..
            }),
        ) = (&entry.value, result_entries.get(key))
        else {
            continue;
        };
        if !now.as_ref().is_some_and(|now| now >= then) {
            return Some(format!(
                "{name} moved the frontier of {:?} at {:?} back: {then:?} then {now:?}",
                key.0, key.1
            ));
        }
    }
    for (label, path) in result_entries.keys() {
        if path.is_empty() {
            continue;
        }
        if collection_of(&last_nodes, label, path).is_some_and(|n| n.absent.contains_path(path)) {
            return Some(format!(
                "{name} holds {label:?} at {path:?}, which it had recorded absent: {last:?} then \
                 {result:?}"
            ));
        }
    }
    for (label, path) in result_entries.keys() {
        if last_entries.contains_key(&(label.clone(), path.clone())) || path.is_empty() {
            continue;
        }
        if collection_of(&last_nodes, label, path).is_some_and(|n| n.complete.contains_path(path)) {
            return Some(format!(
                "{name} added {label:?} at {path:?}, beneath a path it had called complete: \
                 {last:?} then {result:?}"
            ));
        }
    }
    None
}

/// The collection level of `nodes` an entry at `label` and the non-empty `path` sits in: a key's
/// own label, or for a value in a record's field, the label that record's collection was reached
/// by. A key and the scalar value at its path are one entry.
fn collection_of<'a>(
    nodes: &'a HashMap<NodeKey, CompletionNode>,
    label: &[SmolStr],
    path: &[Value],
) -> Option<&'a CompletionNode> {
    let level = path.len() - 1;
    (0..=label.len())
        .rev()
        .find_map(|n| nodes.get(&(label[..n].to_vec(), level)))
}

/// `stated` with every level's `absent_keys` united with `last`'s at the same level, so a record of
/// absence outlives an answer that leaves it out. `stated` holds no key at a path `last` records
/// absent: `completeness_violation` has checked it.
fn keep_recorded_absence(last: &Tile, stated: &mut Tile) {
    match (last, stated) {
        (
            Tile::DataFunction {
                codomain: last_codomain,
                absent_keys: last_absent,
                ..
            },
            Tile::DataFunction {
                codomain,
                absent_keys,
                ..
            },
        ) => {
            *absent_keys = absent_keys.union(last_absent);
            keep_recorded_absence(last_codomain, codomain);
        }
        (
            Tile::Record {
                fields: last_fields,
                ..
            },
            Tile::Record { fields, .. },
        ) => {
            for (field, tile) in fields {
                if let Some(last_field) = last_fields.get(field) {
                    keep_recorded_absence(last_field, tile);
                }
            }
        }
        _ => {}
    }
}

/// Identity, output shape, release state and notification/probe handles for a producer.
#[derive(Clone)]
pub struct ProducerBase {
    /// Instance-unique ID, allocated by [`TileProducer::alloc_id`].
    pub id: usize,
    /// The cell owning this breaker subscription. Weak so the producer cannot retain itself.
    // shared-state-ok: execution ownership metadata; readers still exchange tiles through get.
    pub(crate) breaker_handle: Option<std::sync::Weak<RwLock<dyn BreakingProducer>>>,
    /// The operator that built this producer. `None` for an unprobed forwarding reader
    /// or a protocol test double built with `ProducerBase::unowned`.
    pub node_id: Option<NodeId>,
    /// The probe slot of the subscribe context this producer was subscribed under,
    /// written on every [`TileProducer::get`] while it holds a table.
    pub(crate) probes: ProbeSlot,
    /// Output tiling for this producer.
    pub tiling: Tiling,
    /// Obsolete region of the tiling
    pub obsolete_guard: Arc<RwLock<TileGuard>>,
    #[cfg(test)]
    pub(crate) reads: Arc<std::sync::atomic::AtomicU64>,
    /// The last tile `get` returned, for the debug check that the complete region never
    /// changes ([`completeness_violation`]). Debug builds only; `None` in release.
    pub(crate) last_output: Arc<RwLock<Option<Tile>>>,
    /// For a pipeline breaker, the consumer its pushes climb (`dispatcher::Pushes`), which is
    /// its reader's chain; for a range (`IterateExtent`), the consumer a planner pushes its region
    /// through once. `None` for every other producer.
    pub(crate) downstream: Option<SharedConsumer>,
    /// For a pipeline breaker, the pipeline the [`Entry`](crate::interpreter::dispatcher::Entry)
    /// at its input queues for, which a planner sets. `None` for every other producer.
    pub(crate) placement: Option<crate::interpreter::dispatcher::Placement>,
}

impl ProducerBase {
    /// Initialize a producer for `owner`'s operator.
    pub(crate) fn new(
        id: usize,
        tiling: &Tiling,
        owner: Arc<dyn TileOperator>,
        cx: &SubscribeContext,
    ) -> Self {
        Self {
            id,
            breaker_handle: None,
            node_id: owner.operator_id(),
            probes: cx.probes().clone(),
            tiling: tiling.clone(),
            obsolete_guard: Arc::new(RwLock::new(tiling.empty_guard())),

            #[cfg(test)]
            reads: Arc::new(std::sync::atomic::AtomicU64::new(0)),
            last_output: Arc::new(RwLock::new(None)),
            downstream: None,
            placement: None,
        }
    }

    /// This producer is a pipeline breaker: it pushes to `downstream`, the consumer it was
    /// subscribed with, and the entry at its input queues for the pipeline `placement` names.
    pub(crate) fn breaking(
        mut self,
        downstream: SharedConsumer,
        placement: crate::interpreter::dispatcher::Placement,
    ) -> Self {
        self.downstream = Some(downstream);
        self.placement = Some(placement);
        self
    }

    /// This producer has no input, and a planner pushes its region through `consumer`, the one it
    /// was subscribed with.
    pub(crate) fn leaf(mut self, consumer: SharedConsumer) -> Self {
        self.downstream = Some(consumer);
        self
    }

    /// Push this breaker's work to `consumer`, the head of its reader's chain.
    #[cfg(test)]
    pub(crate) fn pushing_to(&mut self, consumer: SharedConsumer) {
        self.downstream = Some(consumer);
    }

    /// A producer with no operator or probe of its own: a protocol test double or a
    /// forwarding reader whose underlying breaker owns the probe.
    pub(crate) fn unowned(id: usize, tiling: &Tiling) -> Self {
        Self {
            id,
            breaker_handle: None,
            node_id: None,
            probes: ProbeSlot::default(),
            tiling: tiling.clone(),
            obsolete_guard: Arc::new(RwLock::new(tiling.empty_guard())),

            #[cfg(test)]
            reads: Arc::new(std::sync::atomic::AtomicU64::new(0)),
            last_output: Arc::new(RwLock::new(None)),
            downstream: None,
            placement: Some(crate::interpreter::dispatcher::Placement::default()),
        }
    }
}

/// Detach this producer's probe when it goes.
///
/// `LiveProgram::reload`'s teardown drops a replaced version's producers, so
/// their probes go with them, and the probe table never has to decide which
/// entries are still live. An operator the reload kept is not rebuilt, so its
/// producer is not dropped and its probe's readings continue across the swap.
impl Drop for ProducerBase {
    fn drop(&mut self) {
        self.probes.detach(self.node_id, self.id);
    }
}

/// Implement [`TileProducer::base`] and [`TileProducer::base_mut`] for a concrete
/// producer struct that stores its shared state in a field named `base: ProducerBase`.
///
/// Usage: place `impl_producer_base!();` inside the `impl TileProducer for Foo` block
/// in place of the two boilerplate accessor methods.
macro_rules! impl_producer_base {
    () => {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
    };
}
// Re-export the macro within the crate so the cluster submodules can pull it in
// with `use super::impl_producer_base;` — avoiding a `#[macro_export]` that would
// leak it to the crate root.
pub(crate) use impl_producer_base;

/// The debug build's checks on the pulls in progress on this thread: that a producer pulls each
/// input no deeper than its `input_level` declares (`check_input_level`), and that a producer
/// answering from the state `consume_impl` built pulls nothing
/// (`check_not_answering_from_state`).
#[cfg(debug_assertions)]
mod pull_levels {
    use super::{CurryLevel, TileGuard, TileProducer};

    // The pulls in progress on this thread, innermost last, which `check_input_level` and
    // `check_not_answering_from_state` hold each pull against.
    //
    // shared-state-ok: a debug build's record of the pulls on this thread's stack. What crosses it
    // is the level a producer declares for each input and whether the producer answers from state,
    // never a value passed between operators.
    thread_local! {
        // shared-state-ok: the record cell itself, for the reason on the macro above.
        pub(super) static PULLS: std::cell::RefCell<Vec<Pull>> = const { std::cell::RefCell::new(Vec::new()) };
    }

    /// One pull in progress. `levels` is `None` for a pull at no keys, which declares no input
    /// level. `answering` names the producer when it answers from the state `consume_impl` built
    /// ([`TileProducer::answers_from_state`]).
    pub(super) struct Pull {
        levels: Option<PullFrame>,
        answering: Option<String>,
    }

    /// A producer's pull at the keys of a level, with the level it declares for each of its inputs
    /// ([`TileProducer::input_level`]), keyed by the input's address ([`address_of`]). Entering one
    /// records it for the inputs' pulls; dropping it, on return or unwind, removes it.
    pub(super) struct PullFrame {
        producer: String,
        level: CurryLevel,
        inputs: Vec<(usize, String, Option<CurryLevel>)>,
    }

    impl PullFrame {
        pub(super) fn enter(
            producer: &(impl TileProducer + ?Sized),
            guard: &TileGuard,
        ) -> PullScope {
            let levels = match pulled_level(guard) {
                Some(Some(level)) => {
                    let mut inputs = Vec::new();
                    producer.visit_input_producers(&mut |role, input| {
                        inputs.push((address_of(input), role.to_owned(), None));
                    });
                    for (_, role, declared) in &mut inputs {
                        *declared = producer.input_level(role, level);
                    }
                    Some(PullFrame {
                        producer: producer.name(),
                        level,
                        inputs,
                    })
                }
                _ => None,
            };
            let answering = producer.answers_from_state().then(|| producer.name());
            PULLS.with_borrow_mut(|pulls| pulls.push(Pull { levels, answering }));
            PullScope
        }
    }

    /// The pull a [`PullFrame`] records, for as long as it runs.
    pub(super) struct PullScope;

    impl Drop for PullScope {
        fn drop(&mut self) {
            PULLS.with_borrow_mut(|pulls| pulls.pop());
        }
    }

    /// The address a producer is reached at, which its own `get` and its consumer's
    /// `visit_input_producers` agree on.
    pub(super) fn address_of(producer: &(impl TileProducer + ?Sized)) -> usize {
        std::ptr::from_ref(producer).cast::<()>() as usize
    }

    /// The level a pull at `guard` reaches keys at: `Some(level)` for the keys of `level`, and
    /// `Some(None)` for the whole tile. `None` for a pull of nothing, or a guard that names no
    /// projection, which leaves no level to hold a declaration to.
    fn pulled_level(guard: &TileGuard) -> Option<Option<CurryLevel>> {
        use crate::interpreter::Projection;
        match Projection::of(guard) {
            Ok(Projection::Keys { level, .. }) => Some(Some(level)),
            Ok(Projection::Everything) => Some(None),
            Ok(Projection::Nothing) | Err(_) => None,
        }
    }

    /// Panic where the producer at `at` is pulled at `guard` by the producer the innermost pull
    /// records, beneath the level that producer's `input_level` declares for it, or at any keys
    /// where it declares a whole read. `name` names the producer at `at`, and is formatted only for
    /// the panic. The planner checks that each operator of a loop's cycle restates the level its
    /// consumer declares, and stops at an input declared read whole; an operator that restates a
    /// level restates every level above it (`Restates::refuses`). A pull deeper than the
    /// declaration, or at keys of an input declared read whole, is therefore one the planner never
    /// checked. A pull may stop above the declaration: `Uncurry` pulls pairs named by their first
    /// component alone at the input level of that component, the level it pairs at.
    pub(super) fn check_input_level(at: usize, name: impl Fn() -> String, guard: &TileGuard) {
        let Some(pulled) = pulled_level(guard) else {
            return;
        };
        let violation = PULLS.with_borrow(|pulls| {
            let Some(Pull {
                levels: Some(frame),
                ..
            }) = pulls.last()
            else {
                return None;
            };
            let (_, role, declared) = frame.inputs.iter().find(|(input, ..)| *input == at)?;
            let beneath = match (declared, pulled) {
                (_, None) => false,
                (None, Some(_)) => true,
                (Some(declared), Some(pulled)) => pulled > *declared,
            };
            beneath.then(|| {
                let shown = |at: Option<CurryLevel>| match at {
                    Some(at) => format!("the keys of {at}"),
                    None => "a whole read".to_owned(),
                };
                format!(
                    "{} pulled at the keys of {} pulls its input `{role}` ({}) at {}, beneath what \
                     its `input_level` declares, {}",
                    frame.producer,
                    frame.level,
                    name(),
                    shown(pulled),
                    shown(*declared),
                )
            })
        });
        if let Some(violation) = violation {
            panic!("{violation}");
        }
    }

    /// Panic if a pull at `guard` starts while the innermost pull in progress is one of a producer
    /// that answers from the state `consume_impl` built ([`TileProducer::answers_from_state`]),
    /// which pulls nothing. `name` names the pulled producer, and is formatted only for the panic.
    pub(super) fn check_not_answering_from_state(name: impl Fn() -> String, guard: &TileGuard) {
        let answering =
            PULLS.with_borrow(|pulls| pulls.last().and_then(|pull| pull.answering.clone()));
        if let Some(answering) = answering {
            panic!(
                "{answering} answers from the state `consume_impl` built and pulls nothing, but \
                 pulled {} at {guard:?}",
                name()
            );
        }
    }
}

/// Walk the chain under `producer` toward the producers `target` picks, have every producer on a
/// path to one read again the input that leads there ([`TileProducer::read_again`]), and answer
/// whether `producer` is on such a path. `target` answers `Some(true)` at a producer to walk
/// toward, `Some(false)` at one the walk does not descend beneath, and `None` to descend.
///
/// It reaches the producers in `producer`'s chain that a notification of `Everything` climbing the
/// consumers from a picked producer passes. A notification also reaches consumers outside the
/// chain, and a store whose cell is borrowed is not walked into (`FanOutSlot`'s
/// `visit_input_producers_mut`). A producer two paths reach is walked once.
///
/// # Panics
///
/// Where the chain reaches a producer from inside itself: a recurrence slot, the one edge that
/// closes a cycle, visits nothing.
pub(crate) fn read_again_toward(
    producer: &mut dyn TileProducer,
    target: &dyn Fn(&dyn TileProducer) -> Option<bool>,
) -> bool {
    fn walk(
        producer: &mut dyn TileProducer,
        target: &dyn Fn(&dyn TileProducer) -> Option<bool>,
        walked: &mut HashMap<usize, Option<bool>>,
    ) -> bool {
        let address = std::ptr::from_ref::<dyn TileProducer>(producer).cast::<()>() as usize;
        match walked.get(&address) {
            Some(Some(reads)) => return *reads,
            Some(None) => panic!(
                "the walk toward a producer reached {} from inside itself: a chain closes a cycle \
                 only through a recurrence slot, which visits nothing",
                producer.name()
            ),
            None => {}
        }
        walked.insert(address, None);
        let reads = match target(producer) {
            Some(reads) => reads,
            None => {
                let mut inputs = Vec::new();
                producer.visit_input_producers_mut(&mut |input, under| {
                    if walk(under, target, walked) {
                        inputs.push(input.to_owned());
                    }
                });
                for input in &inputs {
                    producer.read_again(input);
                }
                !inputs.is_empty()
            }
        };
        walked.insert(address, Some(reads));
        reads
    }
    walk(producer, target, &mut HashMap::new())
}

/// `held` less `released`, exactly. A guard of a collection's outermost keys, of a scalar and of an
/// aggregation, none of them qualified by an enclosing path, each have a spelling for the
/// difference, and so has a record of such guards, field by field. Two guards of a collection's
/// keys at any levels ([`Projection::of`]) differ as their projections do: a release up to the
/// path `(𝑘, 𝑗)` leaves of the held row `𝑘` its paths past `𝑗`, which `TileGuard::closed_over`
/// drops where the row's level is a finite range with no position past `𝑗`
/// ([`BreakingProducer::final_guard`] closes it). A release with an arm of cells beneath keys,
/// rather than of keys, is taken out of held keys by [`minus_disjoint_arms`], which panics where
/// the difference leaves cells beneath a held key: that difference is a record guard, not the
/// region of keys a breaker pushes. A shape that has no spelling panics: answering a smaller region
/// would claim less than the state holds, and a larger one more.
pub(crate) fn guard_minus(held: &TileGuard, released: &TileGuard) -> TileGuard {
    if released.is_empty() {
        return held.clone();
    }
    match (held, released) {
        (
            TileGuard::Function(FunctionGuard::Domain(held)),
            TileGuard::Function(FunctionGuard::Domain(released)),
        ) if !held.qualifies() && !released.qualifies() => {
            TileGuard::Function(FunctionGuard::Domain(held.minus(released)))
        }
        (TileGuard::Scalar(held), TileGuard::Scalar(released))
            if !held.qualifies() && !released.qualifies() =>
        {
            TileGuard::Scalar(held.minus(released))
        }
        (TileGuard::Aggregation(held), TileGuard::Aggregation(released))
            if !held.qualifies() && !released.qualifies() =>
        {
            TileGuard::Aggregation(held.minus(released))
        }
        (TileGuard::Record(held), TileGuard::Record(released)) => TileGuard::Record(
            held.iter()
                .map(|(name, held)| {
                    let left = match released.get(name) {
                        Some(released) => guard_minus(held, released),
                        None => held.clone(),
                    };
                    (name.clone(), left)
                })
                .collect(),
        ),
        _ => match (Projection::of(held), Projection::of(released)) {
            (Ok(held_keys), Ok(released_keys))
                if names_collection_keys(held) && names_collection_keys(released) =>
            {
                held_keys.minus(&released_keys).collection_guard()
            }
            (Ok(_), Err(_)) if names_collection_keys(held) && names_collection_keys(released) => {
                minus_disjoint_arms(held, released)
            }
            _ => panic!("the guard algebra has no difference of {held:?} and {released:?}"),
        },
    }
}

/// `held`, a guard of a collection's keys, less `released`, an arm of which is a codomain guard
/// naming no keys, such as the cells of some fields of a record beneath a level. The arms of keys
/// ([`keys_released_whole`]) are taken out as projections are ([`guard_minus`]). Every other arm
/// names nothing of what that leaves, so the difference is that region
/// (`src/interpreter/design-path-projections.md`, "Differences of nested guards").
///
/// # Panics
///
/// Where an arm is no projection and no codomain guard, which the algebra has no difference
/// with. Where an arm names a region of what the arms of keys leave: the difference with it is a
/// record guard beneath the held keys, which is no region of keys, and a breaker pushes its final
/// guard as a region of keys.
fn minus_disjoint_arms(held: &TileGuard, released: &TileGuard) -> TileGuard {
    let left = match keys_released_whole(released) {
        Some(keys) => guard_minus(held, &keys),
        None => held.clone(),
    };
    let arms = match released {
        TileGuard::Or(arms) => arms.as_slice(),
        single => std::slice::from_ref(single),
    };
    for arm in arms.iter().filter(|arm| Projection::of(arm).is_err()) {
        assert!(
            left.intersect(arm).is_empty(),
            "the guard algebra has no difference of {held:?} and {released:?} that is a region \
             of keys: the arm {arm:?} names a region of {left:?}"
        );
    }
    left
}

/// The keys `released`, a guard of a collection's keys, names whole: its arms that are regions of
/// keys at any level ([`Projection::of`]), `None` where it has none. Every other arm is a codomain
/// guard naming cells beneath keys, as a selector releases the fields it does not read
/// ([`guard_at_field`](fan)); those keys are not released whole.
///
/// # Panics
///
/// Where `released` is not spelled of a collection's keys, or an arm is neither a region of keys
/// nor a codomain guard.
pub(crate) fn keys_released_whole(released: &TileGuard) -> Option<TileGuard> {
    assert!(
        names_collection_keys(released),
        "a release of a collection's keys, not {released:?}"
    );
    let arms = match released {
        TileGuard::Or(arms) => arms.as_slice(),
        single => std::slice::from_ref(single),
    };
    let (keys, cells): (Vec<TileGuard>, Vec<TileGuard>) = arms
        .iter()
        .cloned()
        .partition(|arm| Projection::of(arm).is_ok());
    for arm in &cells {
        assert!(
            matches!(arm, TileGuard::Function(FunctionGuard::Codomain(_))),
            "the guard algebra has no difference with {released:?}: the arm {arm:?} is no \
             projection and no codomain guard"
        );
    }
    (!keys.is_empty()).then(|| TileGuard::flatten_or(keys))
}

/// Whether `guard` is spelled of a collection's keys: a domain or a codomain guard, or an `Or` of
/// them. [`Projection::of`] reads any universal or empty guard as everything or nothing, whatever
/// it is spelled of, and a difference of a collection's keys with a scalar's is a bug.
fn names_collection_keys(guard: &TileGuard) -> bool {
    match guard {
        TileGuard::Function(_) => true,
        TileGuard::Or(arms) => arms.iter().all(names_collection_keys),
        _ => false,
    }
}

/// `guard`, a guard of `tiling`, cut into morsels of at most `rows` of the `held` keys each, for
/// a breaker that holds a collection: a cut falls before every `rows`-th held key `guard` names,
/// in key order. The morsels partition `guard` exactly, so a key the breaker states absent rides
/// in the morsel that covers it, and a released key is in none because `guard`, a final guard,
/// excludes it. A guard naming no more than `rows` held keys, or one that is not of a
/// collection's outermost keys unqualified, is one morsel.
///
/// # Panics
///
/// When a cut is needed and a held key has no order, such as a function value.
pub(crate) fn cut_at_keys(
    guard: &TileGuard,
    held: impl IntoIterator<Item = Value>,
    rows: usize,
    tiling: &Tiling,
) -> Vec<TileGuard> {
    assert!(rows > 0, "a morsel holds at least one row");
    let (TileGuard::Function(FunctionGuard::Domain(region)), Some(domain)) =
        (guard, tiling.domain_extent())
    else {
        return vec![guard.clone()];
    };
    if region.qualifies() {
        return vec![guard.clone()];
    }
    let mut keys: Vec<Value> = held
        .into_iter()
        .filter(|key| region.contains(key))
        .collect();
    if keys.len() <= rows {
        return vec![guard.clone()];
    }
    if let Some(key) = keys.iter().find(|key| !has_order(key)) {
        panic!("a collection is cut into morsels in key order, which the key {key:?} has none of");
    }
    keys.sort_by(|a, b| {
        a.partial_cmp(b)
            .unwrap_or_else(|| panic!("the keys of one collection compare: {a:?} and {b:?}"))
    });
    keys.dedup();
    let cuts: Vec<Value> = keys.into_iter().skip(rows).step_by(rows).collect();
    cut_before(region, &cuts, &domain)
}

/// Whether `key` has an order among the keys of its type: every value but a function, as
/// `Value`'s `partial_cmp` orders them.
fn has_order(key: &Value) -> bool {
    match key {
        Value::Function(_) | Value::ComputableFunction(_) => false,
        Value::Record(fields) => fields.values().all(has_order),
        Value::Union { inner, .. } => has_order(inner),
        _ => true,
    }
}

/// The region `region` of a collection's outermost keys over `domain`, cut before each of `cuts`,
/// which ascend: the keys below the first cut, then from each cut up to the next, then from the
/// last cut up. Every cut lies in `region`, so each morsel is non-empty but the first, which is
/// non-empty when `region` names a key below the first cut.
pub(crate) fn cut_before(region: &Predicate, cuts: &[Value], domain: &Extent) -> Vec<TileGuard> {
    let mut morsels = Vec::with_capacity(cuts.len() + 1);
    let mut below_last = Predicate::False;
    for cut in cuts {
        let below = Predicate::below_in(cut.clone(), domain);
        morsels.push(region.intersect(&below).minus(&below_last));
        below_last = below;
    }
    morsels.push(region.minus(&below_last));
    morsels
        .into_iter()
        .map(|morsel| TileGuard::Function(FunctionGuard::Domain(morsel)))
        .collect()
}

/// Why `morsels` do not partition `guard`, or `None` when they do: each morsel is non-empty, no
/// two intersect, and their union is `guard`. An empty list partitions exactly an empty guard. One
/// morsel partitions `guard` when it is `guard`; several are guards of a collection's outermost
/// keys.
pub(crate) fn partition_gap(guard: &TileGuard, morsels: &[TileGuard]) -> Option<String> {
    if morsels.is_empty() {
        return (!guard.is_empty()).then(|| format!("no morsel of {guard:?}"));
    }
    if let [only] = morsels {
        return (only != guard).then(|| format!("one morsel {only:?} that is not {guard:?}"));
    }
    let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
        return Some(format!(
            "several morsels of {guard:?}, which has no keys to cut"
        ));
    };
    let mut union = Predicate::False;
    for morsel in morsels {
        let TileGuard::Function(FunctionGuard::Domain(keys)) = morsel else {
            return Some(format!("a morsel {morsel:?} not of outermost keys"));
        };
        if keys.is_false() {
            return Some("an empty morsel".to_string());
        }
        if !union.intersect(keys).is_false() {
            return Some(format!("a morsel {keys:?} that intersects one before it"));
        }
        union = union.union(keys);
    }
    (!(union.subsumes(region) && region.subsumes(&union)))
        .then(|| format!("morsels whose union {union:?} is not {region:?}"))
}

/// The projection of a pull of a producer whose output is one value, which has no keys to project:
/// all of it or none. `what` completes "`name` ..." in the panic: "is one accumulator".
///
/// # Panics
///
/// For a projection of keys.
pub(crate) fn projection_of_one_value(name: &str, what: &str, guard: &TileGuard) -> Projection {
    match guard.projection(name) {
        Projection::Keys { .. } => panic!("{name} {what}, which has no keys to project: {guard:?}"),
        projection => projection,
    }
}

/// Which of a breaker's inputs a work package, a tiling or a release is of, by its index from 0. A
/// breaker of one input has only [`InputId::ONLY`].
#[derive(Clone, Copy)]
pub struct InputId(pub usize);

impl InputId {
    /// The input of a breaker that has one.
    pub const ONLY: InputId = InputId(0);
}

/// The end of a pipeline, as the dispatcher drives it: it consumes the pipeline's work packages.
/// [`consume_impl`] pulls the breaker's input at a guard, merges the answer, and releases the
/// input at what the answer stated once it has taken delivery of it, so the driver handles no
/// tile. A breaker that also answers pulls from that state is a [`BreakingProducer`], which pushes
/// what it decided. When a pipeline may finish is the dispatcher's to decide
/// (`crate::interpreter::dispatcher`). See `src/interpreter/design-operators.md`, "Pipeline
/// breakers".
///
/// [`consume_impl`]: Self::consume_impl
pub trait Breaker {
    /// Projection level at which independent dispatcher claims may consume this breaker.
    fn parallel_level(&self) -> Option<CurryLevel> {
        None
    }

    /// Read the existing input, integrate into synchronized native state, and release
    /// consumed input after dropping the output-state lock.
    fn consume_impl(&self, _input: InputId, _guard: TileGuard) {
        unreachable!("only admitted native breakers consume through shared access")
    }

    fn finish_parallel_input(&mut self) {}

    fn requires_ordered_input(&self) -> bool {
        false
    }

    /// Initialize per-run publication and loop control before the first package executes.
    fn begin_run(&mut self) {}

    /// The tiling of input `input`, which `consume_impl` pulls: what a package's guard is a guard of, and
    /// what a source pipeline's first packages cut.
    fn input_tiling(&self, input: InputId) -> Tiling;

    /// The guard this breaker has released of input `input`, which a finish checks covers every
    /// guard its pipeline consumed.
    fn input_released(&self, input: InputId) -> TileGuard;

    /// The breaker as a producer that other pipelines read: a [`BreakingProducer`] answers
    /// itself, and a breaker that is no producer, such as a sink's, answers `None`. A breaker
    /// that answers `None` pushes nothing, after a consume or at a finish.
    fn as_producer(&self) -> Option<&dyn BreakingProducer>;

    /// Whether the breaker holds a decision it took ahead of its commit and has not settled: a
    /// transaction store's queued decisions and the items it names to decide again. Every step
    /// commits or takes again each decision it takes (`CommitProducer::commit_ready`), so a
    /// drained boundary leaves none, which a reload at one relies on: a writer's drive the reload
    /// rebuilds starts where its predecessor's source release says it stopped. Asserted at every
    /// drained boundary in `drive_live`.
    #[cfg(debug_assertions)]
    fn holds_unsettled_decisions(&self) -> bool {
        false
    }

    /// How many inputs the breaker consumes, each the input of a pipeline of its own: one, but for
    /// a transaction store, which consumes one per writer.
    fn inputs(&self) -> usize {
        1
    }

    /// Have every producer in this breaker's chain that reads the live source `source` read it
    /// again at its next pull: a dispatched run calls it once the source yields more, where the
    /// breaker is a transaction store, whose writer's drive caches what it read of its source. A
    /// no-op for every other breaker.
    fn read_source_again(&mut self, _source: &Arc<RwLock<dyn DataSourceDomainExtentImpl>>) {}

    /// Finish once the pipeline has consumed every package and nothing more can be queued for it,
    /// the breaker's last call. The default pushes what a
    /// producer's [`final_guard`](BreakingProducer::final_guard) names and no push named before,
    /// as one morsel per work package ([`morsels`](BreakingProducer::morsels)); an empty guard
    /// pushes nothing. It wakes no one.
    ///
    /// # Panics
    ///
    /// As [`BreakingProducer::final_guard`].
    fn finish(&mut self, _input: InputId, pushes: &mut Pushes<'_>) {
        if let Some(producer) = self.as_producer() {
            pushes.push_final(producer);
        }
    }
}

/// A pipeline breaker that consumes its input into state and answers reads from that state.
/// `complete` states which output is immutable. After each consume, the driver publishes
/// progress where [`pushes_while_consuming`](Self::pushes_while_consuming) permits it; otherwise
/// it publishes in a later pass. Once the input feeds close and every package is acknowledged,
/// the dispatcher calls [`Breaker::finish`].
/// A placed producer's [`get_impl`](TileProducer::get_impl) reads state without pulling its input.
pub trait BreakingProducer: TileProducer + Breaker {
    /// Store keys whose writers have all completed. Other breakers declare none.
    fn completed_keys(&self) -> Vec<Value> {
        Vec::new()
    }

    /// The complete output region, including keys known absent and output already released.
    /// This statement comes from the breaker's state. Publication and downstream readiness
    /// derive from it; reclaiming payloads must preserve the statement.
    fn complete(&self) -> TileGuard;

    /// The keys under which the producer holds a cell: [`complete`](Self::complete) less the keys its
    /// readers have released whole ([`keys_released_whole`]), closed over the producer's tiling
    /// (`TileGuard::closed_over`), so a row released through its last position is held no more. A
    /// key some of whose cells a reader released, as a selector releases the fields it does not
    /// read, is still held, so a push of the final guard names it. A release of a record, a scalar
    /// or an aggregation is taken out of what is held as [`guard_minus`] takes it.
    ///
    /// # Panics
    ///
    /// Where the guard algebra has no exact difference of what is held and what is released
    /// ([`guard_minus`]), or a release of a collection's keys has an arm that is no region of keys
    /// and no codomain guard ([`keys_released_whole`]).
    fn final_guard(&self) -> TileGuard {
        let held = self.complete();
        let obsolete = self.obsolete_guard();
        let left = match names_collection_keys(&obsolete) {
            true => match keys_released_whole(&obsolete) {
                Some(released) if !held.is_empty() => guard_minus(&held, &released),
                _ => held,
            },
            false => guard_minus(&held, &obsolete),
        };
        left.closed_over(self.tiling())
    }

    /// `guard`, a guard of this producer's tiling it pushes, cut into morsels of at most `rows`
    /// held rows each, which partition `guard` exactly. The default answers `guard` whole, as a
    /// producer whose output is one value does; a producer that holds a collection cuts at its
    /// held outermost keys ([`cut_at_keys`]).
    fn morsels(&self, guard: &TileGuard, _rows: usize) -> Vec<TileGuard> {
        vec![guard.clone()]
    }

    /// Whether a driver publishes this producer's output after each consume. The default
    /// answers `true`. A producer whose publication waits for pipeline completion returns
    /// `false`; its output is published through [`finish`](Breaker::finish).
    /// Loop rounds may publish completed round output through their scope-local pass.
    fn pushes_while_consuming(&self) -> bool {
        true
    }

    /// The placement of the entry at input `input`, which a planner sets to that input's
    /// pipeline. The default answers the producer's own (`ProducerBase::placement`), the entry of
    /// a breaker of one input.
    fn entry_placement(&self, input: InputId) -> Option<crate::interpreter::dispatcher::Placement> {
        debug_assert_eq!(
            input.0,
            0,
            "{} has one input, whose entry its own placement names",
            self.name()
        );
        self.base().placement.clone()
    }

    /// The placements of the entries the producer's seeds are subscribed behind, which a planner
    /// sets to the pipeline of the loop's scope that runs it: an induction store's. Empty for
    /// every other producer.
    fn seed_placements(&self) -> Vec<crate::interpreter::dispatcher::Placement> {
        Vec::new()
    }

    /// The placements of every entry at input `input`, which a planner sets to that input's
    /// pipeline: an input read through several entries, as a transaction store reads one per
    /// seed, has one per entry. The default answers [`entry_placement`](Self::entry_placement).
    fn entry_placements(&self, input: InputId) -> Vec<crate::interpreter::dispatcher::Placement> {
        self.entry_placement(input).into_iter().collect()
    }
}

/// Input rows omitted from an answer, retained until its consumer delivers a release.
#[derive(Default)]
pub(crate) struct DroppedRows(RwLock<Option<TileGuard>>);
impl DroppedRows {
    pub(crate) fn remember(&self, guard: TileGuard) {
        let mut retained = self.0.write().unwrap_or_else(PoisonError::into_inner);
        *retained = Some(match retained.take() {
            Some(before) => before.union(&guard),
            None => guard,
        });
    }
    pub(crate) fn release_to(&self, input: &dyn TileProducer) {
        let released = self
            .0
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        if let Some(guard) = released {
            input.release(guard);
        }
    }
}

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer: Send + Sync {
    /// The entry before `input`, where an enclosing breaker's planner can receive that input's
    /// pushes in its own keys. Unplaced inputs remain read by pull.
    fn input_entry(&self, _input: &str) -> Option<crate::interpreter::dispatcher::Placement> {
        None
    }

    /// Return the shared identity/tiling state for this producer.
    fn base(&self) -> &ProducerBase;

    /// Return the shared identity/tiling state for this producer.
    fn base_mut(&mut self) -> &mut ProducerBase;

    /// Return the [`Tiling`] that describes this producer's output shape.
    fn tiling(&self) -> &Tiling {
        &self.base().tiling
    }

    /// Return the instance-unique numeric ID assigned at construction.
    fn producer_id(&self) -> usize {
        self.base().id
    }

    /// The [`NodeId`] of the operator that built this producer, or `None` for a
    /// producer built outside any [`TileOperator::subscribe`].
    ///
    /// One operator can build several producers — a `FanOut` slot is
    /// subscribed once per slot — so this identifies the operator and not the
    /// instance. [`producer_id`](Self::producer_id) is the instance.
    fn operator_id(&self) -> Option<NodeId> {
        self.base().node_id
    }

    /// Allocate the next instance ID for this producer type.
    ///
    /// The counter key is derived from `Self`'s type name with the `"Producer"`
    /// suffix stripped.  Call this from each producer's constructor to
    /// initialise its `id` field: `id: Self::alloc_id()`.
    fn alloc_id() -> usize
    where
        Self: Sized,
    {
        let raw: &'static str = short_type_name::<Self>();
        let key: &'static str = raw.strip_suffix("Producer").unwrap_or(raw);
        let map = PRODUCER_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut counters = map.lock().unwrap();
        let counter = counters.entry(key).or_insert(0);
        *counter += 1;
        *counter
    }

    /// Return the name of the concrete producer type, disambiguated by instance.
    ///
    /// The default implementation derives the display name from the concrete
    /// type name by stripping the `"Producer"` suffix, then appends `#<id>`.
    /// For example, `MapResultProducer` with id 3 → `"MapResult#3"`.
    fn name(&self) -> String {
        let raw = short_type_name::<Self>();
        let base = raw.strip_suffix("Producer").unwrap_or(raw);
        format!("{}#{}", base, self.producer_id())
    }

    /// Returns the current obsolete guard for this producer. The producer will
    /// never return any more data in the guarded region via `get`.
    fn obsolete_guard(&self) -> TileGuard {
        self.base()
            .obsolete_guard
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// Call [`get_impl`](Self::get_impl), remove released scalar record cells, and check
    /// the result.
    /// Tiling conformance is asserted in every build; release, structural and completeness
    /// checks require debug assertions. Probe observations occur after those checks.
    /// A debug build also checks that the answer holds only what the projection guard names
    /// ([`Tile::within`]); an operator that forwards the projection to its input answers inside
    /// it because the input does, and any other cuts its own answer. It panics on a pull whose
    /// projection names keys at a level [`restates`](Self::restates) refuses.
    /// See `src/interpreter/design-operators.md`, "The producer protocol".
    fn get(&self, projection_guard: TileGuard) -> Tile {
        #[cfg(test)]
        {
            self.base()
                .reads
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        #[cfg(debug_assertions)]
        let _pull = {
            pull_levels::check_not_answering_from_state(|| self.name(), &projection_guard);
            pull_levels::check_input_level(
                pull_levels::address_of(self),
                || self.name(),
                &projection_guard,
            );
            pull_levels::PullFrame::enter(self, &projection_guard)
        };
        let asked = cfg!(debug_assertions).then(|| projection_guard.clone());
        // A producer has no exact answer to a pull at keys it does not restate, so the pull is
        // its consumer's bug.
        if let Some(asked) = &asked
            && let Ok(projection) = Projection::of(asked)
            && let Some(level) = projection.level()
            && self.restates().refuses(level)
        {
            panic!(
                "{} was pulled at {asked:?}, at the keys of {level}, and restates {}",
                self.name(),
                self.restates()
            );
        }
        let mut result = self.get_impl(projection_guard);
        // Released scalar cells are removed while their enclosing rows remain open;
        // see `src/interpreter/design-operators.md`, "The release contract".
        if let Some(cells) = self.obsolete_guard().clone().released_cells() {
            result.remove_guarded(cells);
        }
        // A duplicate scalar delivery can append cells without identifying the repeated
        // positions. Check every released region here, not just universal releases.
        // See `src/interpreter/design-operators.md`, "The release contract".
        debug_assert!(
            !result.contains_guarded(&self.obsolete_guard()),
            "{} returned data it had released: {result:?} overlaps {:?}",
            self.name(),
            self.obsolete_guard(),
        );
        trace!(
            "{} produced {:?} for tiling {}",
            self.name(),
            result,
            self.tiling()
        );
        debug_assert!(validate_tile(&result), "Invalid tile: {result:?}");
        if let Some(asked) = &asked {
            // A guard that is not a projection is left to a producer that restates projections,
            // which panics on it in `get_impl`; one that is, bounds the answer.
            if let Ok(projection) = Projection::of(asked)
                && let Err(outside) = result.within_over(&projection, self.tiling())
            {
                panic!(
                    "{} answered a pull at {asked:?} with {result:?}, but {outside}",
                    self.name()
                );
            }
        }
        if cfg!(debug_assertions) {
            // A pull states completeness only for the region it returns, so the last output
            // is compared inside that region: a producer asked for one region after another
            // withdraws nothing it said of the first.
            let region = asked.as_ref().and_then(|asked| Projection::of(asked).ok());
            let mut history = self
                .base()
                .last_output
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            let last_in_region = history.as_ref().map(|last| {
                let mut last = last.clone();
                if let Some(region) = &region {
                    last.restrict_to(region, self.tiling());
                }
                last
            });
            if let Some(last) = &last_in_region
                && let Some(violation) =
                    completeness_violation(&self.name(), last, &result, &self.obsolete_guard())
            {
                panic!(
                    "{violation}\nin the producer tree:\n{}",
                    crate::pretty_tree::render_with_max_depth(
                        &self.inspect(&VizOptions::default()),
                        Some(6)
                    )
                );
            }
            // The statement a later pull is held to holds each region's last answer: this pull
            // replaces its own region and leaves the others as they were.
            let stated = match (&region, history.take()) {
                (Some(Projection::Nothing), Some(last)) => last,
                (Some(region @ Projection::Keys { .. }), Some(mut last)) => {
                    last.restrict_to(&Projection::Everything.minus(region), self.tiling());
                    // A pull at keys drops from the record what has been released: the
                    // comparison exempts a released row and no later answer holds it.
                    last.remove_guarded(self.obsolete_guard().clone());
                    last.compact();
                    let mut answered = result.clone();
                    answered.restrict_to(region, self.tiling());
                    last.merge(answered);
                    last
                }
                (_, Some(last)) => {
                    let mut stated = result.clone();
                    keep_recorded_absence(&last, &mut stated);
                    stated
                }
                (_, None) => result.clone(),
            };
            *history = Some(stated);
        }
        assert!(
            result.check_from(self.tiling()),
            "{} produced {result:?}, which does not tile as {}",
            self.name(),
            self.tiling()
        );
        // After `get_impl` rather than around it: `get_impl` pulls this
        // producer's inputs, whose own `get` borrows the same probe table, and a
        // read held across that call overlaps the inner one.
        let base = self.base();
        base.probes.observe_named(
            base.node_id,
            base.id,
            || self.name(),
            &result,
            &self.obsolete_guard(),
        );

        result
    }

    /// Produce the tile for `projection_guard`, honoring accumulated releases and completeness.
    /// The [`get`](Self::get) wrapper supplies validation, not general projection or reclamation.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile;

    /// The collection levels whose keys this producer restates. A producer that declares more
    /// than the outermost keys reads its projection with [`TileGuard::projection_for`]
    /// (`src/interpreter/design-path-projections.md`, "Representation").
    fn restates(&self) -> Restates {
        Restates::Outermost
    }

    /// The deepest level a pull of this producer at a projection of the keys of `level` pulls its
    /// input `role` at; `None` where it reads that input whole at every such pull. It is monotone
    /// in `level`: a deeper pull declares no shallower input level. The default passes `level` to
    /// every input, which holds for an operator that keeps its input's keys level for level; an
    /// operator that shifts levels, or reads an input whole, overrides it. The `get` wrapper
    /// checks each pull against the declaration in a debug build (`check_input_level`), and the
    /// planner walks a loop's scope with it to find the levels a round pulls each operator at
    /// (`unrestated` in `dispatcher/plan.rs`).
    fn input_level(&self, _role: &str, level: CurryLevel) -> Option<CurryLevel> {
        Some(level)
    }

    /// Whether a pull of this producer answers from the state `consume_impl` built: `true` for a
    /// breaker that does not read its input ([`ProducerBase::reads_input`]), which is a placed
    /// breaker and any breaker outside a dispatched run, and for a store at every pull; `false`
    /// for every other producer. Such a pull starts no pull of any producer, which the `get`
    /// wrapper checks in a debug build (`check_not_answering_from_state`).
    fn answers_from_state(&self) -> bool {
        false
    }

    /// Permanently release a region after checking its shape and normalizing it.
    /// Accumulate the region in [`obsolete_guard`](Self::obsolete_guard), closed over the tiling
    /// ([`TileGuard::closed_over`]), and deliver every release to [`release_impl`](Self::release_impl), including repeated or empty
    /// releases, so retained input rows discovered by later reads can be reclaimed. Use the
    /// universal guard when the closure makes the stored guard universal, and the normalized
    /// argument otherwise. Native release callbacks must be idempotent. See
    /// `src/interpreter/design-operators.md`, "The release contract".
    fn release(&self, guard: TileGuard) {
        assert!(
            guard.check_from(self.tiling()),
            "{guard:?} vs {:?}",
            self.tiling()
        );
        let guard = TileGuard::flatten_or(vec![guard]);
        let mut obsolete = self
            .base()
            .obsolete_guard
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        let accumulated = obsolete.union(&guard);
        *obsolete = accumulated.closed_over(self.tiling());
        let released = if obsolete.is_universal() {
            self.tiling().universal_guard()
        } else {
            guard
        };
        drop(obsolete);
        self.release_impl(released);
    }

    /// Honor or reject the normalized release argument, already included in the obsolete guard.
    /// Reclaim local state and forward releases according to this operator's input usage.
    /// Ignoring an unsupported guard does not cancel the wrapper's accumulated promise.
    fn release_impl(&self, _obsolete_guard: TileGuard) {
        unreachable!("private control state is released through its producer");
    }

    /// What this producer keeps of its own between pulls ([`ProducerStateInfo`]).
    ///
    /// A producer that keeps nothing past a pull answers the default, which holds nothing.
    /// What its inputs keep is theirs to report.
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::default()
    }

    /// Inspect this producer as an [`InspectNode`] for visualization.
    ///
    /// Always includes name and tiling, and impls can add children with `add_inspect_children`.
    /// A producer holding state records its [`state_info`](Self::state_info) on the node.
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let node = InspectNode::new(self.name()).with_tiling(self.tiling().to_string());
        let node = match self.state_info().values {
            0 => node,
            held => node.with_held_values(held),
        };
        self.add_inspect_children(node, opts)
    }

    /// Hand `visit` each producer this one pulls, with the role it plays. It is what
    /// [`add_inspect_children`](Self::add_inspect_children) lists by default. A producer with
    /// no input visits nothing.
    fn visit_input_producers(&self, _visit: &mut dyn FnMut(&str, &dyn TileProducer)) {}

    /// [`visit_input_producers`](Self::visit_input_producers) with each producer mutable: the
    /// same producers, in the same order, under the same roles. A dispatched run walks it to reach
    /// the pipeline breakers inside a chain ([`as_breaking_mut`](Self::as_breaking_mut)).
    fn visit_input_producers_mut(&mut self, _visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {}

    /// The data sources this producer reads its keys from, where it is a range over a source's
    /// domain: a dispatched run notifies the pipeline above it of what each source yields.
    /// Empty for every other producer.
    fn data_sources(&self) -> Vec<Arc<RwLock<dyn DataSourceDomainExtentImpl>>> {
        Vec::new()
    }

    /// This producer as a pipeline breaker, where it is one.
    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        None
    }

    /// The id of the cyclic fan-out this producer reads through a recurrence slot, where it is
    /// one: an operator inside that fan-out's store's cycle reads the store through it.
    fn recurrence_of(&self) -> Option<usize> {
        None
    }

    /// The cyclic fan-out this producer reads through a reader slot, where it is one: a reader
    /// of that fan-out's store.
    fn store_read(&self) -> Option<StoreRead> {
        None
    }

    fn as_transaction_store(&self) -> Option<&crate::interpreter::commit_operator::CommitProducer> {
        None
    }
    /// The transaction state behind a cyclic store cell, for dispatcher control.
    fn as_transaction_store_mut(
        &mut self,
    ) -> Option<&mut crate::interpreter::commit_operator::CommitProducer> {
        None
    }

    /// The concrete induction store behind a cyclic store cell, where this is one.
    fn as_induction_store(
        &self,
    ) -> Option<&crate::interpreter::commit_operator::InductionStoreProducer> {
        None
    }

    /// The mutable induction state behind a cyclic store cell, where this is one.
    fn as_induction_store_mut(
        &mut self,
    ) -> Option<&mut crate::interpreter::commit_operator::InductionStoreProducer> {
        None
    }

    /// Have every operator inside this producer's cycle read again at its next pull
    /// ([`read_again_toward`]), where it is a store that holds its cycle. A loop's scope has them
    /// read again at the start of each round: the store's last step pulled the operators in pull
    /// mode there, before the round's pipelines took its position.
    fn read_cycle_again(&mut self) {}

    /// Read the input `input` (a role [`visit_input_producers`](Self::visit_input_producers)
    /// names) again at the next pull, where this producer caches what it read of it: a store's
    /// step, or a live source's arrivals, changed what that input answers. A no-op for a producer
    /// that caches nothing.
    fn read_again(&mut self, _input: &str) {}

    /// Where this producer is the drive of a loop run in rounds, the path of the position it emits
    /// next, the next its source delivers, from the outermost level down, and `None` once the
    /// source delivers no more; `None` for any other producer. A loop's scope runs a round per
    /// position the drive emits.
    fn next_position(&self) -> Option<Option<Vec<Value>>> {
        None
    }

    /// Where this producer is a loop's drive, the target the entry in front of its source records
    /// a decided push at while the drive reads the source by pull, and `None` for any other
    /// producer ([`CompletionTarget`](crate::interpreter::dispatcher::CompletionTarget)).
    fn completes_through(&self) -> Option<crate::interpreter::dispatcher::CompletionTarget> {
        None
    }

    /// Take `cycle`, the handle on the cyclic fan-out whose input this producer is. A store
    /// keeps it to publish its snapshot and have its cycle read again while it steps itself as a
    /// pipeline breaker; every other producer ignores it. A cyclic fan-out calls this once, when
    /// its input is subscribed.
    fn enter_cycle(&mut self, _cycle: Cycle) {}

    /// Hook for adding any children to the InspectNode: by default, each producer
    /// [`visit_input_producers`](Self::visit_input_producers) visits, under its role.
    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let mut children = Vec::new();
        self.visit_input_producers(&mut |role, input| {
            children.push((role.to_string(), input.inspect(opts)));
        });
        children
            .into_iter()
            .fold(node, |node, (role, child)| node.child(role, child))
    }
}

/// Values retained by one producer between pulls, excluding its inputs' retained state.
/// The unit is values, not bytes.
/// See `src/interpreter/design-operators.md`, "What a producer holds".
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProducerStateInfo {
    /// The values held: a cached tile's cells ([`Tile::cell_count`]), an accumulator's, or a
    /// store's changelog entries, decided positions and seeds.
    pub values: usize,
}

impl ProducerStateInfo {
    /// `values` held.
    pub fn holding(values: usize) -> Self {
        ProducerStateInfo { values }
    }
}

/// Represents a step on a path through a Tile structure
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TilePathStep {
    /// A step into a specific field of a Record
    Record(SmolStr),
    /// A step into the codomain of a function
    Codomain,
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use std::sync::PoisonError;
    #[derive(Default)]
    pub(crate) struct SharedCounter<T>(std::sync::RwLock<T>);
    impl<T: Copy> SharedCounter<T> {
        pub(crate) fn new(value: T) -> Self {
            Self(std::sync::RwLock::new(value))
        }
        pub(crate) fn get(&self) -> T {
            *self.0.read().unwrap_or_else(PoisonError::into_inner)
        }
        pub(crate) fn set(&self, value: T) {
            *self.0.write().unwrap_or_else(PoisonError::into_inner) = value;
        }
        pub(crate) fn replace(&self, value: T) -> T {
            std::mem::replace(
                &mut *self.0.write().unwrap_or_else(PoisonError::into_inner),
                value,
            )
        }
    }

    #[cfg(test)]
    pub(crate) trait ReadInPipeline: TileProducer {
        fn read_in_pipeline(&mut self, guard: TileGuard) -> Tile {
            crate::interpreter::dispatcher::read_for_test(self, guard)
        }
    }
    #[cfg(test)]
    impl<P: TileProducer + ?Sized> ReadInPipeline for P {}

    #[cfg(test)]
    pub(crate) trait ConsumeInPipeline: super::Breaker {
        fn consume_in_pipeline(&mut self, input: super::InputId, guard: TileGuard) {
            if let Some(producer) = self.as_producer()
                && let Some(placement) = &producer.base().placement
            {
                placement.set(Some(crate::interpreter::dispatcher::PipelineId(0)));
            }
            crate::interpreter::dispatcher::in_pipeline_for_test(|| {
                self.consume_impl(input, guard)
            });
        }
    }
    impl<P: super::Breaker + ?Sized> ConsumeInPipeline for P {}

    pub(crate) trait Announce: super::Consumer {
        fn announce(&mut self, region: &Projection) {
            crate::interpreter::dispatcher::notify_for_test(self, region);
        }
    }
    #[cfg(test)]
    impl<C: super::Consumer + ?Sized> Announce for C {}

    use super::{
        InspectNode, ProducerBase, Tile, TileGuard, TileOperator, TileProducer, Tiling, VizOptions,
    };
    use crate::interpreter::{ColumnValue, FunctionGuard, Predicate, Projection, Value};
    use bit_set::BitSet;
    use intervalsets::{Interval, IntervalSet};

    /// Push `breaker`'s work into the queues of `readers`, pipelines whose breakers read it with
    /// nothing between, as an [`Entry`](crate::interpreter::dispatcher::Entry) at the input of
    /// each does: the reader's input is the breaker itself, so its tiling is the breaker's.
    pub(crate) fn push_to(breaker: &mut dyn TileProducer, readers: &[usize]) {
        use crate::interpreter::dispatcher::{Entry, PipelineId};
        let input = breaker.tiling().clone();
        let entries = readers
            .iter()
            .map(|&reader| Entry::new(PipelineId(reader), input.clone()))
            .collect();
        breaker
            .base_mut()
            .pushing_to(std::sync::Arc::new(std::sync::RwLock::new(Readers(
                entries,
            ))));
    }

    /// Point each breaker's pushes at the pipelines that read it in `reads`, whose breakers read
    /// it with nothing between ([`push_to`]).
    pub(crate) fn wire(
        reads: &[Vec<usize>],
        breakers: &[crate::interpreter::dispatcher::BreakerHandle],
    ) {
        for (pipeline, breaker) in breakers.iter().enumerate() {
            let readers: Vec<usize> = (0..reads.len())
                .filter(|reader| reads[*reader].contains(&pipeline))
                .collect();
            if !readers.is_empty() {
                push_to(
                    &mut *breaker.write().unwrap_or_else(PoisonError::into_inner),
                    &readers,
                );
            }
        }
    }

    /// The entries of the pipelines that read one breaker: a push reaches each.
    struct Readers(Vec<crate::interpreter::dispatcher::Entry>);

    impl crate::interpreter::Consumer for Readers {
        fn notify(
            &mut self,
            region: &Projection,
            landing: &mut crate::interpreter::dispatcher::Landing<'_>,
        ) {
            for entry in &mut self.0 {
                crate::interpreter::Consumer::notify(entry, region, landing);
            }
        }
    }

    /// The projection guard naming the keys `[first, last]` of the outermost collection.
    pub(crate) fn keys_between(first: u64, last: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
            IntervalSet::from(Interval::closed(Value::UInt(first), Value::UInt(last))),
        )))
    }

    /// `values` as a collection of integers keyed by position `0..`, stating `complete` of its
    /// whole domain or only of the positions it holds.
    pub(crate) fn ints_by_position(values: &[i64], complete: bool) -> Tile {
        let domain_predicate = match (complete, values.len()) {
            (true, _) => Predicate::True,
            (false, 0) => Predicate::False,
            (false, n) => Predicate::at_or_below(Value::UInt(n as u64 - 1)),
        };
        Tile::data_function(
            ColumnValue::UInts((0..values.len() as u64).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(values.to_vec()))),
            domain_predicate,
            BitSet::new(),
        )
    }

    /// The `(position, value)` entries of a collection of integers keyed by position, in key
    /// order, whatever order the tile holds them in. A row the tile marks deleted is not an
    /// entry, as it is to a consumer.
    pub(crate) fn int_entries(tile: &Tile) -> Vec<(u64, i64)> {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = tile
        else {
            panic!("a collection, got {tile:?}");
        };
        let (ColumnValue::UInts(keys), Tile::Scalar(ColumnValue::Ints(values))) =
            (domain, codomain.as_ref())
        else {
            panic!("positions to integers, got {tile:?}");
        };
        let mut entries: Vec<(u64, i64)> = keys
            .iter()
            .copied()
            .zip(values.iter().copied())
            .enumerate()
            .filter(|(row, _)| !deleted.contains(*row))
            .map(|(_, entry)| entry)
            .collect();
        entries.sort_unstable();
        entries
    }

    /// `k ⤇ j ⤇ Int`: the keys 0 and 1, each holding the positions 0 to 2 valued `10k + j`, every
    /// level stated complete, and its tiling. The input a test of a projection beneath the
    /// outermost keys pulls.
    pub(crate) fn two_levels_of_ints() -> (Tile, Tiling) {
        use crate::interpreter::{BaseType, Extent};
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::UInts(vec![0, 1, 2, 0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 2, 10, 11, 12]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        (tile, tiling)
    }

    /// The guard naming the paths `(k, j)` of a two-level collection that `paths` admits, a
    /// predicate over `j` qualified by `k`.
    pub(crate) fn paths_guard(paths: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
            FunctionGuard::Domain(paths),
        ))))
    }

    /// Assert that the producer of each operator `make` builds, over two levels of keys, answers
    /// a pull at a projection of paths as the whole of its answer cut to it
    /// ([`assert_conforms`]): one path, and paths of two rows.
    pub(crate) fn assert_conforms_beneath(make: impl Fn() -> std::sync::Arc<dyn TileOperator>) {
        let point = |k: u64| Predicate::point(Value::UInt(k));
        for paths in [
            Predicate::qualified(point(0), point(1)),
            Predicate::qualified(point(0), point(2))
                .union(&Predicate::qualified(point(1), point(0))),
        ] {
            assert_conforms(
                || {
                    let op = make();
                    let guard = op.tiling().universal_guard();
                    op.clone().subscribe(
                        guard,
                        Box::new(|| {}),
                        &mut super::SubscribeContext::new(),
                    )
                },
                paths_guard(paths),
            );
        }
    }

    /// Assert that a producer answers a projection as the whole of its answer cut to it. `make`
    /// builds the same producer twice: one is pulled at `guard`, the other at the universal
    /// guard, and the second's tile is cut to `guard` and compared. Both are compacted and
    /// ordered by key where the keys are scalars, since a producer may order its rows as it likes.
    pub(crate) fn assert_conforms(make: impl Fn() -> Box<dyn TileProducer>, guard: TileGuard) {
        let normal = |mut tile: Tile| {
            tile.compact();
            // Pairs and other record keys keep the order the producer gave them.
            match &tile {
                Tile::DataFunction {
                    domain: ColumnValue::Records(_),
                    ..
                } => tile,
                _ => crate::interpreter::sort_function_by_domain(tile),
            }
        };
        let mut projected = make();
        let answer = normal(projected.read_in_pipeline(guard.clone()));
        let mut whole = make();
        let mut expected = whole.read_in_pipeline(whole.tiling().universal_guard());
        expected.restrict_to(
            &Projection::of(&guard).expect("assert_conforms takes a projection guard"),
            whole.tiling(),
        );
        assert_eq!(
            answer,
            normal(expected),
            "a pull at {guard:?} is the whole answer cut to it"
        );
    }

    /// A [`TileProducer`] that **conforms to projection**: it answers a fixed tile minus what
    /// has been released, cut to the projection guard it is pulled with. It logs every
    /// projection and every release it receives, which is how a test sees the guard an
    /// operator restated for its input.
    ///
    /// Pull it after releasing, never over a region already pulled and kept: the double is
    /// itself held to the completeness contract.
    pub(crate) struct ProjectionSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        /// The tile it answers from instead of `tile`, which a test rewrites between pulls to
        /// grow its input.
        script: Option<std::sync::Arc<std::sync::RwLock<Tile>>>,
        pub(crate) pulled: GuardLog,
        pub(crate) released: GuardLog,
    }

    /// The two logs of a [`ProjectionSpy`]: the projection guards it was pulled with, and the
    /// guards released to it.
    pub(crate) type GuardLog = std::sync::Arc<std::sync::RwLock<Vec<TileGuard>>>;

    impl ProjectionSpy {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, GuardLog, GuardLog) {
            let pulled = GuardLog::default();
            let released = GuardLog::default();
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    script: None,
                    pulled: pulled.clone(),
                    released: released.clone(),
                },
                pulled,
                released,
            )
        }

        /// A spy that answers what the returned cell holds, which a test rewrites between pulls to
        /// grow the input.
        pub(crate) fn scripted(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::sync::Arc<std::sync::RwLock<Tile>>) {
            let (mut spy, _, _) = Self::new(tile.clone(), tiling);
            let cell = std::sync::Arc::new(std::sync::RwLock::new(tile));
            spy.script = Some(cell.clone());
            (spy, cell)
        }
    }

    impl TileProducer for ProjectionSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn restates(&self) -> crate::interpreter::Restates {
            crate::interpreter::Restates::Every
        }

        fn get_impl(&self, projection_guard: TileGuard) -> Tile {
            self.pulled
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(projection_guard.clone());
            let mut tile = match &self.script {
                Some(script) => script
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone(),
                None => self.tile.clone(),
            };
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            let projection = projection_guard.projection_for(self);
            tile.restrict_to(&projection, self.tiling());
            tile
        }

        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(obsolete_guard);
        }
    }

    /// An operator over a fixed tile whose producers are [`ProjectionSpy`]s sharing one pair of
    /// logs, so a test can build a fan-out or a memo over it and read what reaches the input.
    pub(crate) struct ProjectionSpyOp {
        tile: Tile,
        tiling: Tiling,
        pulled: GuardLog,
        released: GuardLog,
    }

    impl ProjectionSpyOp {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, GuardLog, GuardLog) {
            let (pulled, released) = (GuardLog::default(), GuardLog::default());
            (
                Self {
                    tile,
                    tiling,
                    pulled: pulled.clone(),
                    released: released.clone(),
                },
                pulled,
                released,
            )
        }
    }

    impl TileOperator for ProjectionSpyOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn super::Consumer>,
            _cx: &mut super::SubscribeContext,
        ) -> Box<dyn TileProducer> {
            let (mut spy, _, _) = ProjectionSpy::new(self.tile.clone(), self.tiling.clone());
            spy.pulled = self.pulled.clone();
            spy.released = self.released.clone();
            Box::new(spy)
        }
    }

    /// A test helper TileProducer that returns a pre-determined tile.
    /// Useful for testing TileOperators by injecting tiles directly.
    pub(crate) struct TestTileProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
    }

    impl TestTileProducer {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> Self {
            Self {
                base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                tile,
            }
        }
    }

    /// A collection of `Int` keyed by `keys`, each key holding its own value, with `decided`
    /// stated complete.
    pub(crate) fn int_column(keys: Vec<u64>, decided: Predicate) -> Tile {
        let values = keys.iter().map(|&key| key as i64).collect();
        Tile::data_function(
            ColumnValue::from_uints(keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            decided,
            BitSet::new(),
        )
    }

    /// A [`TileProducer`] that answers each pull with the tile its shared cell holds, cut to
    /// the projection and minus what has been released to it, so a test can change its input
    /// between pulls. What a producer states on one pull
    /// constrains what it may answer on the next (`src/interpreter/design-operators.md`,
    /// "The completeness contract"), which a fixed tile cannot exercise.
    pub(crate) struct ScriptedProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: std::sync::Arc<std::sync::RwLock<Tile>>,
    }

    impl ScriptedProducer {
        /// The producer, and the cell a test writes the next pull's answer into.
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::sync::Arc<std::sync::RwLock<Tile>>) {
            let cell = std::sync::Arc::new(std::sync::RwLock::new(tile));
            let producer = Self {
                base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                tile: cell.clone(),
            };
            (producer, cell)
        }
    }

    impl TileProducer for ScriptedProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, projection_guard: TileGuard) -> Tile {
            let mut tile = self
                .tile
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            let projection = projection_guard.projection("ScriptedProducer");
            tile.restrict_to(&projection, self.tiling());
            tile
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// An operator whose producer is a [`ScriptedProducer`] over a cell the test keeps, so a
    /// test can feed a growing input through a real consumer. The producer answers the cell
    /// minus what has been released to it.
    pub(crate) struct ScriptedOp {
        cell: std::sync::Arc<std::sync::RwLock<Tile>>,
        tiling: Tiling,
    }

    impl ScriptedOp {
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::sync::Arc<std::sync::RwLock<Tile>>) {
            let cell = std::sync::Arc::new(std::sync::RwLock::new(tile));
            (
                Self {
                    cell: cell.clone(),
                    tiling,
                },
                cell,
            )
        }
    }

    impl TileOperator for ScriptedOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn super::Consumer>,
            _cx: &mut super::SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(ScriptedProducer {
                base: ProducerBase::unowned(ScriptedProducer::alloc_id(), &self.tiling),
                tile: self.cell.clone(),
            })
        }
    }

    /// A consumer that logs the region of each notification it receives.
    pub(crate) struct RegionLog {
        regions: std::sync::Arc<std::sync::RwLock<Vec<Projection>>>,
    }

    impl RegionLog {
        pub(crate) fn new() -> (Self, std::sync::Arc<std::sync::RwLock<Vec<Projection>>>) {
            let regions = std::sync::Arc::new(std::sync::RwLock::new(Vec::new()));
            (
                Self {
                    regions: regions.clone(),
                },
                regions,
            )
        }
    }

    impl super::Consumer for RegionLog {
        fn notify(
            &mut self,
            region: &Projection,
            _: &mut crate::interpreter::dispatcher::Landing<'_>,
        ) {
            self.regions
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(region.clone());
        }
    }

    /// The consumer a [`NotifyingOp`] was subscribed with, which a test notifies through.
    pub(crate) type InputConsumer =
        std::sync::Arc<std::sync::RwLock<Option<Box<dyn super::Consumer>>>>;

    /// An operator over a fixed tile that keeps the consumer it is subscribed with, so a test
    /// notifies an operator above it from where the operator's input would.
    pub(crate) struct NotifyingOp {
        tile: Tile,
        tiling: Tiling,
        consumer: InputConsumer,
        script: Option<std::sync::Arc<std::sync::RwLock<Tile>>>,
        pulled: GuardLog,
    }

    impl NotifyingOp {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, InputConsumer) {
            let consumer = InputConsumer::default();
            (
                Self {
                    tile,
                    tiling,
                    consumer: consumer.clone(),
                    script: None,
                    pulled: GuardLog::default(),
                },
                consumer,
            )
        }

        /// An operator whose producer answers what the returned cell holds, cut to the guard it
        /// is pulled with, so a test grows its input between pulls, and the log of the guards
        /// it was pulled with.
        pub(crate) fn scripted(
            tile: Tile,
            tiling: Tiling,
        ) -> (
            Self,
            InputConsumer,
            std::sync::Arc<std::sync::RwLock<Tile>>,
            GuardLog,
        ) {
            let (mut op, consumer) = Self::new(tile.clone(), tiling);
            let cell = std::sync::Arc::new(std::sync::RwLock::new(tile));
            op.script = Some(cell.clone());
            let pulled = op.pulled.clone();
            (op, consumer, cell, pulled)
        }
    }

    impl TileOperator for NotifyingOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            consumer: Box<dyn super::Consumer>,
            _cx: &mut super::SubscribeContext,
        ) -> Box<dyn TileProducer> {
            *self
                .consumer
                .write()
                .unwrap_or_else(PoisonError::into_inner) = Some(consumer);
            let (mut spy, _, _) = ProjectionSpy::new(self.tile.clone(), self.tiling.clone());
            spy.script = self.script.clone();
            spy.pulled = self.pulled.clone();
            Box::new(spy)
        }
    }

    /// Notify through the consumer a [`NotifyingOp`] was subscribed with.
    pub(crate) fn notify_input(consumer: &InputConsumer, arrived: &Projection) {
        crate::interpreter::dispatcher::notify_for_test(
            &mut **consumer
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .as_mut()
                .unwrap(),
            arrived,
        );
    }

    /// A store's parts are collections held to the contract like any other: a decided set
    /// stated `True` that gains a position has added a key beneath a complete path. The same
    /// growth under a statement naming only what is decided passes.
    #[test]
    fn a_store_part_growing_beneath_its_own_statement_is_reported() {
        use crate::interpreter::commit_operator::{CommitEngine, full_store_tiling};
        use crate::interpreter::operator_conversion::store_key;
        use crate::interpreter::{BaseType, Extent, FunctionGuard, Position, Predicate, Value};
        use std::collections::HashMap;
        let tiling = full_store_tiling(
            Extent::Base(BaseType::UInt),
            HashMap::from([("acc".into(), Tiling::Scalar(Extent::Base(BaseType::Int)))]),
        );
        let mut engine = CommitEngine::unopened();
        let step = |engine: &mut CommitEngine, p: u64| {
            let writes = HashMap::from([(
                store_key(&crate::ccl::Label::new("acc")),
                Value::Int(p as i64),
            )]);
            engine.step(Position::new(Value::UInt(p)), Some(writes));
            engine.render_full_store_tile(&tiling)
        };
        let last = step(&mut engine, 0);
        let result = step(&mut engine, 1);
        let released = TileGuard::Function(FunctionGuard::Domain(Predicate::False));
        assert_eq!(
            super::completeness_violation("honest", &last, &result, &released),
            None
        );

        let claim_all = |mut tile: Tile| {
            if let Tile::Store { decided, .. } = &mut tile
                && let Tile::DataFunction {
                    domain_predicate, ..
                } = &mut **decided
            {
                *domain_predicate = Predicate::True;
            }
            tile
        };
        let message = super::completeness_violation(
            "claims_all",
            &claim_all(last.clone()),
            &claim_all(result.clone()),
            &released,
        )
        .expect("a decided set stated whole while it grows is reported");
        assert!(
            message.contains("#decided")
                && message.contains("beneath a path it had called complete"),
            "{message}"
        );
    }

    /// A value in a record's field filled in beneath a key already called complete is an
    /// addition beneath a complete path, which the completeness contract forbids.
    #[test]
    fn a_record_field_filled_beneath_a_complete_key_is_reported() {
        use crate::interpreter::{ColumnValue, Predicate};
        use bit_set::BitSet;
        use std::collections::HashMap;
        let with_n = |n: ColumnValue| {
            // Built directly rather than through `Tile::data_function`, which a tile holding
            // a complete key with an empty field need not pass: this is the check's input.
            Tile::DataFunction {
                row_starts: vec![0],
                domain: ColumnValue::UInts(vec![0]),
                codomain: Box::new(Tile::record(HashMap::from([
                    ("n".into(), Tile::Scalar(n)),
                    (
                        "xs".into(),
                        Tile::grouped(
                            vec![0],
                            ColumnValue::UInts(vec![]),
                            Box::new(Tile::Scalar(ColumnValue::UInts(vec![]))),
                            Predicate::False,
                            BitSet::new(),
                        ),
                    ),
                ]))),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
                absent_keys: Predicate::False,
            }
        };
        let last = with_n(ColumnValue::Ints(vec![]));
        let result = with_n(ColumnValue::Ints(vec![5]));
        let violation = super::completeness_violation(
            "a_record_field",
            &last,
            &result,
            &TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
        )
        .expect("an addition beneath a complete key is reported");
        assert!(
            violation.contains("beneath a path it had called complete"),
            "{violation}"
        );
    }

    /// A stream of `0..8` whose answer holds the keys `from..=to` and states `stated` complete.
    fn answered(from: u64, to: u64, stated: (u64, u64)) -> (Tile, Tiling) {
        use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Value};
        use bit_set::BitSet;
        let region = |first: u64, last: u64| {
            Predicate::intervals(IntervalSet::from(Interval::closed(
                Value::UInt(first),
                Value::UInt(last),
            )))
        };
        let tile = Tile::data_function(
            ColumnValue::from_uints((from..=to).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                (from..=to).map(|key| key as i64).collect(),
            ))),
            region(stated.0, stated.1),
            BitSet::new(),
        );
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        (tile, tiling)
    }

    /// `tile`, an answer of [`answered`], recording the keys `absent` absent in every region.
    fn recording_absent(mut tile: Tile, absent: &[u64]) -> Tile {
        use crate::interpreter::{Predicate, Value};
        let Tile::DataFunction { absent_keys, .. } = &mut tile else {
            unreachable!("a collection")
        };
        *absent_keys = absent.iter().fold(Predicate::False, |all, &key| {
            all.union(&Predicate::point(Value::UInt(key)))
        });
        tile
    }

    /// A producer that records a key absent and later holds it, in the region it was pulled at
    /// when it recorded it, has broken the record.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "which it had recorded absent")]
    fn a_producer_that_holds_a_key_it_recorded_absent_is_reported() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let (first, tiling) = answered(0, 1, (0, 1));
        let (producer, answer) = ScriptedProducer::new(recording_absent(first, &[5]), tiling);
        producer.get(producer.tiling().universal_guard());
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(0, 5, (0, 1)).0;
        producer.get(producer.tiling().universal_guard());
    }

    /// The record of absence holds in every region: a pull of another region that holds a key
    /// recorded absent at the first breaks it.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "which it had recorded absent")]
    fn a_key_recorded_absent_at_one_region_and_held_at_another_is_reported() {
        use crate::interpreter::tile_operators::test_helpers::{ScriptedProducer, keys_between};
        let (first, tiling) = answered(0, 1, (0, 1));
        let (producer, answer) = ScriptedProducer::new(recording_absent(first, &[5]), tiling);
        producer.get(keys_between(0, 1));
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(4, 7, (4, 7)).0;
        producer.get(keys_between(4, 7));
    }

    /// An answer may leave out the keys recorded absent: the record is not withdrawn by it.
    #[test]
    fn an_answer_that_leaves_out_the_record_of_absence_withdraws_nothing() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let (first, tiling) = answered(0, 1, (0, 1));
        let (producer, answer) =
            ScriptedProducer::new(recording_absent(first.clone(), &[5]), tiling);
        producer.get(producer.tiling().universal_guard());
        *answer.write().unwrap_or_else(PoisonError::into_inner) = first;
        producer.get(producer.tiling().universal_guard());
    }

    /// The record of absence outlives an answer that leaves it out: a third answer holding the key
    /// breaks it.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "which it had recorded absent")]
    fn a_key_held_after_an_answer_that_left_out_its_absence_is_reported() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let (first, tiling) = answered(0, 1, (0, 1));
        let (producer, answer) =
            ScriptedProducer::new(recording_absent(first.clone(), &[5]), tiling);
        producer.get(producer.tiling().universal_guard());
        *answer.write().unwrap_or_else(PoisonError::into_inner) = first;
        producer.get(producer.tiling().universal_guard());
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(0, 5, (0, 1)).0;
        producer.get(producer.tiling().universal_guard());
    }

    /// A key held beneath an enclosing key at a path recorded absent there breaks the record,
    /// which is read at the whole path.
    #[test]
    fn a_key_held_at_a_nested_path_recorded_absent_is_reported() {
        use crate::interpreter::{ColumnValue, Predicate, Value};
        use bit_set::BitSet;
        // Outer keys `0` and `1`, holding `inner` beneath `0` and nothing beneath `1`.
        let groups = |inner: Vec<u64>, absent: Predicate| Tile::DataFunction {
            row_starts: vec![0],
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::DataFunction {
                row_starts: vec![0, inner.len()],
                domain: ColumnValue::UInts(inner.clone()),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(
                    inner.iter().map(|&v| v as i64).collect(),
                ))),
                domain_predicate: Predicate::False,
                deleted: BitSet::new(),
                absent_keys: absent,
            }),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
            absent_keys: Predicate::False,
        };
        let four_under_zero = Predicate::qualified(
            Predicate::point(Value::UInt(0)),
            Predicate::point(Value::UInt(4)),
        );
        let last = groups(vec![3], four_under_zero);
        let result = groups(vec![3, 4], Predicate::False);
        let violation = super::completeness_violation(
            "groups",
            &last,
            &result,
            &TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
        )
        .expect("a key at a nested path recorded absent is reported");
        assert!(
            violation.contains("which it had recorded absent"),
            "{violation}"
        );
    }

    /// A producer pulled at one region after another keeps what it stated of each: a pull of a
    /// disjoint region between two pulls of the first withdraws nothing, and answering the first
    /// again as it did passes.
    #[test]
    fn a_producer_asked_for_two_regions_in_turn_may_repeat_its_first_answer() {
        use crate::interpreter::tile_operators::test_helpers::{ScriptedProducer, keys_between};
        let (first, tiling) = answered(0, 3, (0, 3));
        let (producer, answer) = ScriptedProducer::new(first.clone(), tiling);
        producer.get(keys_between(0, 3));
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(4, 7, (4, 7)).0;
        producer.get(keys_between(4, 7));
        *answer.write().unwrap_or_else(PoisonError::into_inner) = first;
        producer.get(keys_between(0, 3));
    }

    /// An input that states a region complete, answers a pull of another region, and then
    /// retracts the first when it is pulled there again has broken the contract, though the
    /// pull before the retraction was at the other region.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "withdrew completion")]
    fn a_producer_that_retracts_a_region_after_a_pull_of_another_is_reported() {
        use crate::interpreter::tile_operators::test_helpers::{ScriptedProducer, keys_between};
        let (first, tiling) = answered(0, 3, (0, 3));
        let (producer, answer) = ScriptedProducer::new(first, tiling);
        producer.get(keys_between(0, 3));
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(4, 7, (4, 7)).0;
        producer.get(keys_between(4, 7));
        *answer.write().unwrap_or_else(PoisonError::into_inner) = answered(0, 3, (0, 1)).0;
        producer.get(keys_between(0, 3));
    }

    #[test]
    fn a_release_of_other_keys_does_not_wait_for_an_in_flight_read() {
        use std::sync::{
            Mutex, RwLock,
            atomic::{AtomicBool, Ordering},
            mpsc,
        };
        use std::time::Duration;

        struct PausedSnapshot {
            base: ProducerBase,
            tile: RwLock<Tile>,
            pause_next_read: AtomicBool,
            entered: mpsc::Sender<()>,
            released: Mutex<mpsc::Receiver<()>>,
        }
        impl TileProducer for PausedSnapshot {
            impl_producer_base!();
            fn get_impl(&self, guard: TileGuard) -> Tile {
                let mut tile = self.tile.read().unwrap().clone();
                tile.restrict_to(&guard.projection_for(self), self.tiling());
                if self.pause_next_read.swap(false, Ordering::SeqCst) {
                    self.entered.send(()).unwrap();
                    self.released
                        .lock()
                        .unwrap()
                        .recv_timeout(Duration::from_secs(10))
                        .expect("releasing another key must not wait for this read");
                }
                tile
            }
            fn release_impl(&self, guard: TileGuard) {
                let mut tile = self.tile.write().unwrap();
                tile.remove_guarded(guard);
                tile.compact();
            }
        }

        let tiling = Tiling::data_function(
            crate::interpreter::Extent::uint_range(2),
            Tiling::Scalar(crate::interpreter::Extent::Base(
                crate::interpreter::BaseType::Int,
            )),
        );
        let (entered, started) = mpsc::channel();
        let (finished, released) = mpsc::channel();
        let producer = PausedSnapshot {
            base: ProducerBase::unowned(PausedSnapshot::alloc_id(), &tiling),
            tile: RwLock::new(int_column(vec![0, 1], Predicate::True)),
            pause_next_read: AtomicBool::new(true),
            entered,
            released: Mutex::new(released),
        };
        let first = keys_between(0, 0);
        let second = keys_between(1, 1);
        std::thread::scope(|scope| {
            let reader = scope.spawn(|| producer.get(first));
            started.recv_timeout(Duration::from_secs(10)).unwrap();
            let reclaimer = scope.spawn(|| {
                producer.release(second.clone());
                finished.send(()).unwrap();
            });
            reclaimer.join().unwrap();
            let answer = reader.join().unwrap();
            let Tile::DataFunction { domain, .. } = answer else {
                panic!("a collection snapshot")
            };
            assert_eq!(domain, ColumnValue::UInts(vec![0]));
        });
        assert!(producer.obsolete_guard().subsumes(&second));
        assert!(!producer.tile.read().unwrap().contains_guarded(&second));
    }

    /// A [`TileProducer`] that answers with a fixed tile, less what it has been released, and
    /// records every release guard it is handed, for asserting that a release *propagates*.
    pub(crate) struct ReleaseSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        pub(crate) released: std::sync::Arc<std::sync::RwLock<Vec<TileGuard>>>,
    }

    impl ReleaseSpy {
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::sync::Arc<std::sync::RwLock<Vec<TileGuard>>>) {
            let released = std::sync::Arc::new(std::sync::RwLock::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    released: released.clone(),
                },
                released,
            )
        }
    }

    impl TileProducer for ReleaseSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(obsolete_guard);
        }
    }

    impl TileProducer for TestTileProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// A [`TileProducer`] that **honors** the release contract: it answers with a
    /// fixed tile minus everything released so far, and logs each guard handed to
    /// it.
    ///
    /// Use this over [`ReleaseSpy`] whenever a test pulls again *after* releasing.
    /// A double that re-answers released rows is itself the contract violation, so
    /// the assertion in [`TileProducer::get`] fires on the double before the
    /// behavior under test is ever reached.
    pub(crate) struct QuietSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        pub(crate) released: std::sync::Arc<std::sync::RwLock<Vec<TileGuard>>>,
    }

    impl QuietSpy {
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::sync::Arc<std::sync::RwLock<Vec<TileGuard>>>) {
            let released = std::sync::Arc::new(std::sync::RwLock::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    released: released.clone(),
                },
                released,
            )
        }
    }

    impl TileProducer for QuietSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            let mut tile = self.tile.clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            tile
        }

        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(obsolete_guard);
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(debug_assertions)]
    use super::test_helpers::ReadInPipeline as _;
    use super::{
        Consumer, InputEdgeSpec, OperatorBase, ProducerBase, SubscribeContext, Tile, TileGuard,
        TileOperator, TileProducer, Tiling,
    };
    use crate::interpreter::{Extent, types::BaseType, types::ColumnValue};

    fn int_tiling() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    /// A producer over a two-level collection that pulls its input at member 1 under every row
    /// whatever it is pulled at, and keeps the default `input_level`, which declares the level
    /// it is pulled at.
    #[cfg(debug_assertions)]
    struct Deepening {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    #[cfg(debug_assertions)]
    impl TileProducer for Deepening {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            use super::FunctionGuard;
            use crate::interpreter::{Predicate, Value};
            self.input
                .get(TileGuard::Function(FunctionGuard::Codomain(Box::new(
                    TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(1)))),
                ))))
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    #[cfg(debug_assertions)]
    fn deepening() -> (Deepening, Tiling) {
        let (tile, tiling) = super::test_helpers::two_levels_of_ints();
        let (input, ..) = super::test_helpers::ProjectionSpy::new(tile, tiling.clone());
        let deepening = Deepening {
            base: ProducerBase::unowned(Deepening::alloc_id(), &tiling),
            input: Box::new(input),
        };
        (deepening, tiling)
    }

    /// A producer pulled at the outermost keys that pulls its input beneath them, where its
    /// `input_level` declares the outermost keys, fails the `get` wrapper's check.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "beneath what its `input_level` declares, the keys of level 0")]
    fn a_pull_beneath_the_declared_input_level_panics() {
        use super::FunctionGuard;
        use crate::interpreter::{Predicate, Value};
        let (mut deepening, _) = deepening();
        deepening.read_in_pipeline(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::UInt(0)),
        )));
    }

    /// The record of pulls in progress is emptied when a pull unwinds, so a later pull is held
    /// against its own consumer's declaration rather than the one that panicked.
    #[test]
    #[cfg(debug_assertions)]
    fn a_pull_that_unwinds_leaves_no_record_behind() {
        use super::FunctionGuard;
        use crate::interpreter::{Predicate, Value};
        let (deepening, tiling) = deepening();
        let outermost =
            TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(0))));
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            deepening.get(outermost.clone())
        }));
        assert!(unwound.is_err(), "the pull beneath its declaration panics");
        assert!(super::pull_levels::PULLS.with_borrow(Vec::is_empty));
        let (tile, _) = super::test_helpers::two_levels_of_ints();
        let (input, ..) = super::test_helpers::ProjectionSpy::new(tile, tiling);
        input.get(outermost);
    }

    /// A producer that reports it answers from state ([`TileProducer::answers_from_state`]) and
    /// pulls its input at the guard it is pulled at, which such a producer may not.
    #[cfg(debug_assertions)]
    struct PullingStateAnswer {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    #[cfg(debug_assertions)]
    impl TileProducer for PullingStateAnswer {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn answers_from_state(&self) -> bool {
            true
        }

        fn get_impl(&self, projection_guard: TileGuard) -> Tile {
            self.input.get(projection_guard)
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    #[cfg(debug_assertions)]
    fn pulling_state_answer() -> (PullingStateAnswer, Tiling) {
        let (tile, tiling) = super::test_helpers::two_levels_of_ints();
        let (input, ..) = super::test_helpers::ProjectionSpy::new(tile, tiling.clone());
        let answer = PullingStateAnswer {
            base: ProducerBase::unowned(PullingStateAnswer::alloc_id(), &tiling),
            input: Box::new(input),
        };
        (answer, tiling)
    }

    /// A producer answering from the state `consume_impl` built that pulls its input fails the
    /// `get` wrapper's check, which names both producers.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(
        expected = "answers from the state `consume_impl` built and pulls nothing, but \
                               pulled ProjectionSpy"
    )]
    fn an_answer_from_state_that_pulls_its_input_panics() {
        let (answer, tiling) = pulling_state_answer();
        answer.get(tiling.universal_guard());
    }

    /// A pull answering from state is taken off the record of pulls in progress when it unwinds,
    /// so a later pull on the same thread is not held to it.
    #[test]
    #[cfg(debug_assertions)]
    fn an_answer_from_state_that_unwinds_leaves_no_record_behind() {
        let (answer, tiling) = pulling_state_answer();
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            answer.get(tiling.universal_guard())
        }));
        assert!(unwound.is_err(), "the answer from state that pulls panics");
        assert!(super::pull_levels::PULLS.with_borrow(Vec::is_empty));
        let (tile, _) = super::test_helpers::two_levels_of_ints();
        let (input, ..) = super::test_helpers::ProjectionSpy::new(tile, tiling.clone());
        input.get(tiling.universal_guard());
    }

    /// A producer that pulls a [`PullingStateAnswer`] under `catch_unwind` and then its own input,
    /// recording how many pulls are in progress after the unwind.
    #[cfg(debug_assertions)]
    struct CatchingPull {
        base: ProducerBase,
        answer: PullingStateAnswer,
        input: Box<dyn TileProducer>,
        in_progress_after_unwind: std::sync::RwLock<Option<usize>>,
    }

    #[cfg(debug_assertions)]
    impl TileProducer for CatchingPull {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("answer", &self.answer);
            visit("input", &*self.input);
        }

        fn get_impl(&self, projection_guard: TileGuard) -> Tile {
            let whole = self.answer.tiling().universal_guard();
            let unwound =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.answer.get(whole)));
            assert!(unwound.is_err(), "the answer from state that pulls panics");
            *self.in_progress_after_unwind.write().unwrap() =
                Some(super::pull_levels::PULLS.with_borrow(Vec::len));
            self.input.get(projection_guard)
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// An answer from state that unwinds inside another pull leaves that pull's record in place,
    /// and the pull goes on to pull its own input.
    #[test]
    #[cfg(debug_assertions)]
    fn an_answer_from_state_that_unwinds_inside_a_pull_restores_that_pull() {
        let (answer, tiling) = pulling_state_answer();
        let (tile, _) = super::test_helpers::two_levels_of_ints();
        let (input, ..) = super::test_helpers::ProjectionSpy::new(tile, tiling.clone());
        let outer = CatchingPull {
            base: ProducerBase::unowned(CatchingPull::alloc_id(), &tiling),
            answer,
            input: Box::new(input),
            in_progress_after_unwind: std::sync::RwLock::new(None),
        };
        outer.get(tiling.universal_guard());
        assert_eq!(
            *outer.in_progress_after_unwind.read().unwrap(),
            Some(1),
            "the outer pull alone is in progress"
        );
        assert!(super::pull_levels::PULLS.with_borrow(Vec::is_empty));
    }

    struct OneRow {
        base: ProducerBase,
    }

    impl TileProducer for OneRow {
        impl_producer_base!();

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            Tile::Scalar(ColumnValue::Ints(vec![7]))
        }

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    struct Leaf {
        base: OperatorBase,
    }

    impl TileOperator for Leaf {
        impl_operator_base!();

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(OneRow {
                base: ProducerBase::new(OneRow::alloc_id(), &self.base.tiling, self.clone(), cx),
            })
        }
    }

    /// A producer subscribed before probing is switched on is probed once it
    /// is, under its operator's id: probes attach on demand, not at build.
    #[test]
    fn a_producer_is_probed_under_its_operator_once_its_subscribe_context_enables_probing() {
        let op = std::sync::Arc::new(Leaf {
            base: OperatorBase::new(int_tiling()),
        });
        let mut cx = SubscribeContext::new();
        let producer =
            op.clone()
                .subscribe(int_tiling().universal_guard(), Box::new(|| {}), &mut cx);
        assert_eq!(producer.operator_id(), op.operator_id());

        producer.get(int_tiling().universal_guard());
        assert!(!cx.probes().is_enabled());

        cx.probes().enable();
        producer.get(int_tiling().universal_guard());
        let keys: Vec<_> = cx
            .probes()
            .with_table(|table| table.probe_keys().collect())
            .expect("probing is on");
        assert_eq!(keys, vec![(op.operator_id(), producer.producer_id())]);

        drop(producer);
        assert_eq!(
            cx.probes().with_table(|table| table.probe_keys().count()),
            Some(0),
            "dropping a producer detaches its probe",
        );
    }

    /// The difference of two guards of a breaker's state, where the algebra can spell it exactly.
    mod guard_difference {
        use super::super::{TileGuard, guard_minus, keys_released_whole};
        use crate::interpreter::{FunctionGuard, Predicate, Value};
        use intervalsets::{Interval, IntervalSet};
        use std::collections::HashMap;

        fn keys(first: u64, last: u64) -> Predicate {
            Predicate::intervals(IntervalSet::from(Interval::closed(
                Value::UInt(first),
                Value::UInt(last),
            )))
        }

        fn domain(predicate: Predicate) -> TileGuard {
            TileGuard::Function(FunctionGuard::Domain(predicate))
        }

        /// Nothing released leaves any guard as it is, whatever its shape.
        #[test]
        fn nothing_released_leaves_any_shape() {
            let nested = TileGuard::Or(vec![domain(Predicate::True), domain(keys(1, 2))]);
            assert_eq!(guard_minus(&nested, &domain(Predicate::False)), nested);
        }

        #[test]
        fn outermost_keys_scalars_and_aggregations_have_a_difference() {
            assert_eq!(
                guard_minus(&domain(Predicate::True), &domain(keys(2, 3))),
                domain(Predicate::True.minus(&keys(2, 3)))
            );
            assert_eq!(
                guard_minus(
                    &TileGuard::Scalar(Predicate::True),
                    &TileGuard::Scalar(Predicate::True)
                ),
                TileGuard::Scalar(Predicate::False)
            );
            assert_eq!(
                guard_minus(
                    &TileGuard::Aggregation(Predicate::True),
                    &TileGuard::Aggregation(Predicate::True)
                ),
                TileGuard::Aggregation(Predicate::False)
            );
        }

        /// A record is exact field by field: a field the release does not name is kept whole.
        #[test]
        fn a_record_is_exact_per_field() {
            let held = TileGuard::Record(HashMap::from([
                ("a".into(), domain(Predicate::True)),
                ("b".into(), TileGuard::Scalar(Predicate::True)),
            ]));
            let released = TileGuard::Record(HashMap::from([("a".into(), domain(keys(0, 4)))]));
            let left = guard_minus(&held, &released);
            assert_eq!(
                left,
                TileGuard::Record(HashMap::from([
                    ("a".into(), domain(Predicate::True.minus(&keys(0, 4)))),
                    ("b".into(), TileGuard::Scalar(Predicate::True)),
                ]))
            );
        }

        /// A release beneath the keys of a group leaves every key's paths it does not name.
        #[test]
        fn a_release_beneath_a_group_leaves_the_paths_it_does_not_name() {
            let beneath =
                TileGuard::Function(FunctionGuard::Codomain(Box::new(domain(keys(0, 1)))));
            assert_eq!(
                guard_minus(&domain(Predicate::True), &beneath),
                TileGuard::Function(FunctionGuard::Codomain(Box::new(domain(
                    Predicate::True.minus(&keys(0, 1))
                ))))
            );
        }

        /// A key of the outermost collection qualified by an enclosing path names no region, and
        /// the difference names the gap.
        #[test]
        #[should_panic(expected = "the guard algebra has no difference")]
        fn a_qualified_predicate_has_no_difference() {
            let qualified = Predicate::Qualified {
                enclosing: Box::new(keys(1, 1)),
                here: Box::new(keys(0, 2)),
            };
            guard_minus(&domain(Predicate::True), &domain(qualified));
        }

        /// The cells of the fields `_0` and `_1` that `first` and `second` name, beneath every key
        /// of a stream of records.
        fn record_cells(first: TileGuard, second: TileGuard) -> TileGuard {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Record(
                HashMap::from([("_0".into(), first), ("_1".into(), second)]),
            ))))
        }

        /// A release of a key whole and of a field's cells beneath that key, which the meet of a
        /// `FanOut`'s readers releases, leaves the keys the first arm leaves.
        #[test]
        fn a_release_of_cells_beneath_a_released_key_leaves_the_other_keys() {
            let beneath_zero = Predicate::qualified(keys(0, 0), Predicate::True);
            let released = TileGuard::Or(vec![
                domain(keys(0, 0)),
                record_cells(TileGuard::Scalar(Predicate::False), domain(beneath_zero)),
            ]);
            assert_eq!(
                guard_minus(&domain(Predicate::True), &released),
                domain(Predicate::True.minus(&keys(0, 0)))
            );
        }

        /// A release of one field's cells under keys still held leaves those keys' other cells,
        /// which a record guard beneath the keys names and a guard of keys does not.
        #[test]
        #[should_panic(expected = "that is a region of keys")]
        fn a_release_of_cells_of_a_held_key_has_no_difference() {
            let released = TileGuard::Or(vec![
                domain(keys(0, 0)),
                record_cells(
                    TileGuard::Scalar(Predicate::True),
                    TileGuard::Scalar(Predicate::False),
                ),
            ]);
            guard_minus(&domain(keys(0, 1)), &released);
        }

        /// A release's arms of keys, at any level, are the keys it names whole; an arm of cells
        /// beneath keys names none.
        #[test]
        fn the_keys_a_release_names_whole_leave_out_its_cells() {
            let cells = record_cells(
                TileGuard::Scalar(Predicate::True),
                TileGuard::Scalar(Predicate::False),
            );
            let released = TileGuard::Or(vec![domain(keys(0, 0)), cells.clone()]);
            assert_eq!(keys_released_whole(&released), Some(domain(keys(0, 0))));
            assert_eq!(keys_released_whole(&cells), None);
        }

        /// A release of cells alone, not in an `Or`, beneath keys not held leaves what is held.
        #[test]
        fn a_release_of_cells_alone_beneath_keys_not_held_leaves_what_is_held() {
            let beneath_zero = Predicate::qualified(keys(0, 0), Predicate::True);
            let released = record_cells(TileGuard::Scalar(Predicate::False), domain(beneath_zero));
            assert_eq!(
                guard_minus(&domain(keys(1, 1)), &released),
                domain(keys(1, 1))
            );
        }

        /// A domain guard qualified by more enclosing levels than it steps into is no projection
        /// and no codomain guard, so `guard_minus` panics.
        #[test]
        #[should_panic(expected = "is no projection and no codomain guard")]
        fn a_release_arm_that_is_no_codomain_guard_has_no_difference() {
            let qualified = Predicate::qualified(keys(1, 1), keys(0, 2));
            let released = TileGuard::Or(vec![domain(keys(0, 0)), domain(qualified)]);
            guard_minus(&domain(Predicate::True), &released);
        }

        /// `paths` beneath the keys: a guard of level 1.
        fn beneath(paths: Predicate) -> TileGuard {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(domain(paths))))
        }

        /// The cells of field `_0` of a stream of records two levels deep, beneath the paths
        /// `paths` names.
        fn first_field_beneath(paths: &TileGuard) -> TileGuard {
            let first = TileGuard::Function(FunctionGuard::Codomain(Box::new(record_cells(
                TileGuard::Scalar(Predicate::True),
                TileGuard::Scalar(Predicate::False),
            ))));
            first.intersect(paths)
        }

        /// A held row of paths released at a path whole and at a field's cells beneath that path
        /// holds the paths the first arm leaves.
        #[test]
        fn a_release_of_cells_beneath_a_released_path_leaves_the_other_paths() {
            let path = |j| beneath(Predicate::qualified(keys(0, 0), keys(j, j)));
            let released = TileGuard::Or(vec![path(0), first_field_beneath(&path(0))]);
            assert_eq!(
                guard_minus(
                    &beneath(Predicate::qualified(keys(0, 0), keys(0, 1))),
                    &released
                ),
                path(1)
            );
        }

        /// A release of a field's cells beneath a held path leaves that path's other cells.
        #[test]
        #[should_panic(expected = "that is a region of keys")]
        fn a_release_of_cells_beneath_a_held_path_has_no_difference() {
            let path = |j| beneath(Predicate::qualified(keys(0, 0), keys(j, j)));
            let released = TileGuard::Or(vec![path(0), first_field_beneath(&path(1))]);
            guard_minus(
                &beneath(Predicate::qualified(keys(0, 0), keys(0, 1))),
                &released,
            );
        }
    }
}

/// Independent position claims of a native input. Nested materialization retains whole rows.
fn parallel_input_level(input: &dyn TileProducer, inner: bool) -> Option<CurryLevel> {
    let tiling = input.tiling();
    let level = if matches!(tiling.domain_extent(), Some(Extent::UIntRange(_))) {
        CurryLevel::OUTERMOST
    } else if inner
        && matches!(tiling,
        Tiling::DataFunction { codomain, .. }
        if matches!(&**codomain, Tiling::DataFunction { domain: Extent::UIntRange(_), .. }))
    {
        CurryLevel::new(1)
    } else {
        return None;
    };
    (!input.restates().refuses(level)).then_some(level)
}
