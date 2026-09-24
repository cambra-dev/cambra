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

use std::{
    cell::Cell,
    collections::HashMap,
    rc::Rc,
    sync::{Mutex, OnceLock},
};

use log::trace;

pub use crate::interpreter::tiling::{
    CurryLevel, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
};
use crate::{
    ccl::provenance::NodeId,
    interpreter::operator_graph::{EdgeKind, InputEdgeSpec},
    interpreter::{ColumnValue, Consumer, Extent, Scheduler, Value, validate_tile},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

mod aggregate;
mod combinators;
mod cycle_slot;
mod extract_final;
mod fan;
mod fanout;
mod helpers;
mod iterate;
mod lookup;
mod map;
mod reshape;
mod scalar;
mod union;

pub use aggregate::*;
pub use combinators::*;
pub use cycle_slot::*;
pub use extract_final::*;
pub use fan::*;
pub use fanout::*;
pub use helpers::*;
pub use iterate::*;
pub use lookup::*;
pub use map::*;
pub use reshape::*;
pub use scalar::*;
pub use union::*;

/// Static descriptor of a computation node in the tile dataflow graph.
///
/// An operator knows its output [`Tiling`] and can instantiate a live
/// [`TileProducer`] by subscribing a [`Consumer`].  Operators are
/// constructed at compile time; producers are created on demand at runtime.
pub trait TileOperator {
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
    /// through an `RefCell`: the borrow lives for the call and cannot outlive
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

    /// Subscribe to this operator with an intent guard and consumer.
    /// Returns a producer that allows the consumer to get data and release regions.
    ///
    /// # Arguments
    /// * `intent_guard` - The region of the operator's extent that the consumer
    ///   is interested in
    /// * `consumer` - The consumer that will receive notifications when data is ready
    /// * `scheduler` - The scheduler that coordinates source triggering and
    ///   inter-operator work during execution.
    ///
    /// # Returns
    /// A producer that provides access to the data and allows releasing regions
    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer>;

    /// Render this operator and what it holds as an [`InspectNode`].
    ///
    /// The children are [`visit_inputs`](Self::visit_inputs)' `Value` edges, so
    /// an operator states what it holds once and this reads the same answer the
    /// graph walk does. `Share` edges are left out: a fan branch's edge to its
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

/// Whether a producer's input has notified it since the producer last pulled.
///
/// A [`Consumer::notify`](crate::interpreter::Consumer) says new data is available and
/// carries no payload, so it is the only signal a producer can act on without pulling.
/// The flag is set by the consumer handle an operator installs on its own input
/// ([`Self::consumer`]) and cleared by a pull, so a producer whose input has said nothing
/// since it last read knows there is nothing to read.
///
/// Held behind an `Rc<Cell<_>>` because the setter and the reader are built at different
/// times: `subscribe` must hand the input a consumer before it has a producer to put the
/// flag in.
///
/// A producer instance has exactly one consumer — sharing goes through a
/// [`FanOut`](crate::interpreter::tile_operators::FanOut), whose branches are separate
/// producers with separate flags — so "since the consumer last pulled" and "since anyone
/// last pulled" are the same statement.
#[derive(Clone)]
pub enum Notified {
    /// The input's notification does not reach this producer, so every pull reads —
    /// what an operator whose `subscribe` installs no flag gets.
    Always,
    /// Set when the input notifies, cleared by a pull.
    // shared-state-ok: see the type doc.
    Flag(Rc<Cell<bool>>),
}

impl Notified {
    /// A live [`Flag`](Self::Flag), starting set: a producer that has never pulled has
    /// everything to read.
    pub fn flag() -> Self {
        Self::Flag(Rc::new(Cell::new(true)))
    }

    /// Record that the input has new data.
    pub fn mark(&self) {
        if let Self::Flag(c) = self {
            c.set(true);
        }
    }

    /// Read and clear. `Always` reads set and stays set.
    pub fn take(&self) -> bool {
        match self {
            Self::Always => true,
            Self::Flag(c) => c.replace(false),
        }
    }

    /// A consumer handle that sets this flag and then passes the notification on.
    ///
    /// Installed on a producer's own input so the notification reaches the operator
    /// rather than running straight from source to sink past it.
    pub fn consumer(&self, downstream: Box<dyn Consumer>) -> Box<dyn Consumer> {
        let flag = self.clone();
        let mut downstream = downstream;
        Box::new(move || {
            flag.mark();
            downstream.notify();
        })
    }
}

/// One collection level of a tile, keyed in [`completion_view`]'s map by the record fields
/// walked through to reach it and its collection depth. `complete` is the
/// region of paths reaching this level the tile calls complete — its own statement, and
/// the one above read a level further in, since a complete key is complete beneath.
struct CompletionNode {
    complete: Predicate,
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

type NodeKey = (Vec<String>, usize);
type EntryKey = (Vec<String>, Vec<Value>);

/// Flatten `tile` into its collection levels and the entries it holds.
fn completion_view(tile: &Tile) -> (HashMap<NodeKey, CompletionNode>, HashMap<EntryKey, Entry>) {
    fn walk(
        tile: &Tile,
        label: &[String],
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
            } => {
                let complete = match level {
                    0 => domain_predicate.clone(),
                    _ => {
                        Predicate::qualified(above.clone(), Predicate::True).union(domain_predicate)
                    }
                };
                let ColumnValue::UInts(starts) = row_starts else {
                    unreachable!("a collection's row starts are positions")
                };
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
                nodes.insert((label.to_vec(), level), CompletionNode { complete });
            }
            Tile::Record(fields) => {
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
                            complete: level > 0 && above.contains_path(path),
                        },
                    );
                }
            }
            // A store's row is what it answers: its frontier, each key's seed, and each
            // key's value at every position it has decided. Its changelog is only how it
            // answers — reclaiming a released prefix keeps every carry source a live
            // position folds to, so the answers outside what was released do not move.
            Tile::Store { .. } if level > 0 => {
                use crate::interpreter::commit_operator::{
                    store_decided_positions, store_frontier, store_seed_value, store_value_at,
                };
                use crate::interpreter::operator_conversion::store_key;
                for (row, path) in rows.iter().enumerate() {
                    let Some(path) = path else { continue };
                    let one = tile.select_rows(&[row]);
                    let complete = level > 0 && above.contains_path(path);
                    let entry = |value: EntryValue| Entry { value, complete };
                    let at_label = |name: &str| {
                        let mut l = label.to_vec();
                        l.push(name.to_string());
                        l
                    };
                    entries.insert(
                        (at_label("frontier"), path.clone()),
                        entry(EntryValue::Frontier(store_frontier(&one))),
                    );
                    let Tile::Store { decided, .. } = &one else {
                        unreachable!("a store's rows are stores")
                    };
                    let positions = store_decided_positions(decided, 0);
                    let names: Vec<String> = one.store_keys().cloned().collect();
                    for name in names {
                        let key = store_key(&name, Value::Unit);
                        entries.insert(
                            (at_label(&format!("seed.{name}")), path.clone()),
                            entry(EntryValue::Value(store_seed_value(&one, &key))),
                        );
                        for position in &positions {
                            let mut at = path.clone();
                            at.push(position.value().clone());
                            entries.insert(
                                (at_label(&name), at),
                                entry(EntryValue::Value(store_value_at(&one, position, &key))),
                            );
                        }
                    }
                }
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

/// The paths reaching collection level `level` under record fields `label` that `guard`
/// releases: a domain guard `d` codomain steps in names keys of level `d` and everything
/// beneath them.
fn released_at(guard: &TileGuard, label: &[String], level: usize) -> Predicate {
    fn walk(guard: &TileGuard, label: &[String], depth: usize, level: usize) -> Predicate {
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
            TileGuard::Function(FunctionGuard::Domain(pred)) if depth <= level => (depth..level)
                .fold(pred.clone(), |region, _| {
                    Predicate::qualified(region, Predicate::True)
                }),
            _ => Predicate::False,
        }
    }
    walk(guard, label, 0, level)
}

/// Assert that `result` leaves unchanged everything `last` called complete, apart from
/// removing what `released` has released since: the two rules of
/// `src/interpreter/design-operators.md`, "The completeness contract".
///
/// A statement covers every path at its level, including paths under rows that have not
/// arrived, so the second rule applies to them too: a key appearing under a row called
/// complete before it arrived breaks it.
pub(crate) fn assert_complete_region_unchanged(
    name: &str,
    last: &Tile,
    result: &Tile,
    released: &TileGuard,
) {
    let (last_nodes, last_entries) = completion_view(last);
    let (result_nodes, result_entries) = completion_view(result);
    for ((label, level), node) in &last_nodes {
        let released_here = released_at(released, label, *level);
        let promised = node.complete.minus(&released_here);
        let kept = result_nodes
            .get(&(label.clone(), *level))
            .map_or(Predicate::False, |n| n.complete.clone());
        assert!(
            kept.subsumes(&promised),
            "{name} withdrew completion at level {level} of {label:?}: it called {promised:?} \
             complete, and now calls only {kept:?} complete"
        );
    }
    let is_released = |label: &Vec<String>, path: &Vec<Value>| {
        !path.is_empty() && released_at(released, label, path.len() - 1).contains_path(path)
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
            now => panic!(
                "{name} changed {label:?} at {path:?}, which it had called complete: {:?} \
                 then {:?}, in {last:?} then {result:?}, having released {released:?}",
                entry.value,
                now.map(|n| &n.value)
            ),
        }
    }
    for (label, path) in result_entries.keys() {
        if last_entries.contains_key(&(label.clone(), path.clone())) || path.is_empty() {
            continue;
        }
        // The collection an entry sits in: a key's own label, or for a value in a record's
        // field, the label that record's collection was reached by.
        let level = path.len() - 1;
        let was_complete = (0..=label.len())
            .rev()
            .find_map(|n| last_nodes.get(&(label[..n].to_vec(), level)))
            .is_some_and(|n| n.complete.contains_path(path));
        assert!(
            !was_complete,
            "{name} added {label:?} at {path:?}, beneath a path it had called complete: \
             {last:?} then {result:?}"
        );
    }
}

/// Common identity and tiling state shared by every [`TileProducer`].
///
/// Storing these together avoids repeating the same two fields and their
/// trivial accessor implementations across every producer struct.
pub struct ProducerBase {
    /// Instance-unique ID, allocated by [`TileProducer::alloc_id`].
    pub id: usize,
    /// Output tiling for this producer.
    pub tiling: Tiling,
    /// Obsolete region of the tiling
    pub obsolete_guard: TileGuard,
    pub(crate) notified: Notified,
    /// The last tile `get` returned, for the debug check that the complete region never
    /// changes ([`assert_complete_region_unchanged`]). Debug builds only; `None` in release.
    pub(crate) last_output: Option<Tile>,
}

impl ProducerBase {
    /// A producer whose input notification does not reach it, so every pull reads.
    pub(crate) fn new(id: usize, tiling: &Tiling) -> Self {
        Self::listening(id, tiling, Notified::Always)
    }

    /// A producer that reads only when its input has said something since its last
    /// pull. `notified` is the flag whose [`Notified::consumer`] this producer's
    /// `subscribe` installed on its input.
    pub(crate) fn listening(id: usize, tiling: &Tiling, notified: Notified) -> Self {
        Self {
            id,
            tiling: tiling.clone(),
            obsolete_guard: tiling.empty_guard(),
            notified,
            last_output: None,
        }
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

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer {
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
    /// For example, `MapApplyProducer` with id 3 → `"MapApply#3"`.
    fn name(&self) -> String {
        let raw = short_type_name::<Self>();
        let base = raw.strip_suffix("Producer").unwrap_or(raw);
        format!("{}#{}", base, self.producer_id())
    }

    /// Returns the current obsolete guard for this producer. The producer will
    /// never return any more data in the guarded region via `get`.
    fn obsolete_guard(&self) -> &TileGuard {
        &self.base().obsolete_guard
    }

    /// Fetch the current tile value.  Contains generic logic for all producers
    fn get(&mut self, projection_guard: TileGuard) -> Tile {
        let result = self.get_impl(projection_guard);
        // A release says that data is never requested and never returned again.
        // Being pulled afterwards is fine — the answer is whatever lies outside
        // the released region, which after a universal release is nothing at all
        // — so what has to hold is this post-condition, at every granularity
        // rather than only the universal one.
        //
        // Returning released data breaks things *silently*, which is why it is
        // checked centrally rather than left to each operator: a consumer that
        // has already taken delivery merges the same values a second time, and a
        // `Tile::Scalar`'s positions are implicit, so merge cannot tell "this
        // position again" from "one more position" and appends. One value becomes
        // two, and it surfaces at whichever downstream consumer broadcasts the
        // result rather than here.
        debug_assert!(
            !result.contains_guarded(self.obsolete_guard()),
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
        if cfg!(debug_assertions) {
            if let Some(last) = &self.base().last_output
                && std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    assert_complete_region_unchanged(
                        &self.name(),
                        last,
                        &result,
                        self.obsolete_guard(),
                    )
                }))
                .is_err()
            {
                panic!(
                    "the panic above, raised checking the completeness contract, in the \
                     producer tree:\n{}",
                    crate::pretty_tree::render_with_max_depth(
                        &self.inspect(&VizOptions::default()),
                        Some(6)
                    )
                );
            }
            self.base_mut().last_output = Some(result.clone());
        }
        assert!(
            result.check_from(self.tiling()),
            "{} produced {result:?}, which does not tile as {}",
            self.name(),
            self.tiling()
        );
        result
    }

    /// Fetch the current tile value.  Producer-specific logic
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile;

    /// Release interest in a region.
    /// The `obsolete_guard` specifies a sub-region of the subscription that
    /// is no longer needed. Returns an expanded obsolete guard that may be
    /// larger if the producer has additional obsolescence information (e.g.,
    /// from variables with their own obsolete guards).
    fn release(&mut self, obsolete_guard: TileGuard) {
        trace!("{} release: {obsolete_guard:?}", self.name());
        assert!(
            obsolete_guard.check_from(self.tiling()),
            "{obsolete_guard:?} vs {:?}",
            self.tiling()
        );
        // Released in canonical form (`TileGuard::flatten_or`), so a region naming everything
        // beneath some keys reaches `release_impl` as those keys.
        let obsolete_guard = TileGuard::flatten_or(vec![obsolete_guard]);
        let new_guard = self.base().obsolete_guard.union(&obsolete_guard);
        if new_guard != self.base().obsolete_guard {
            self.base_mut().obsolete_guard = new_guard;
            self.release_impl(obsolete_guard);
        }
    }

    /// Release interest in a region.
    /// Contains producer-specific release logic.
    fn release_impl(&mut self, obsolete_guard: TileGuard);

    /// Inspect this producer as an [`InspectNode`] for visualization.
    ///
    /// Always includes name and tiling, and impls can add children with `add_inspect_children`
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        self.add_inspect_children(
            InspectNode::new(self.name()).with_tiling(self.tiling().to_string()),
            opts,
        )
    }

    /// Hook for adding any children to the InspectNode.
    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }
}

/// A producer that participates in a cyclic operator graph as an **append-only,
/// position-stable sequencing source** — the commit operator's recurrence (and
/// the changelog induction store) rely on this contract:
///
/// 1. Its output tile is append-only along the sequencing domain: a value once
///    emitted at a position is never changed (only `release` shrinks the view).
/// 2. Positions are absolute and never shift; a released prefix may be compacted
///    away, but the live suffix keeps its position values.
/// 3. Because a released prefix desyncs a fanned branch, a stateful sequencing
///    producer is wired with exactly one consumer (the cycle uses
///    [`FanOut::new_cyclic`] around the *operator*; the producer itself is never
///    fanned). Fanning one is a wiring bug, not a user error.
/// 4. `release` is the acknowledgment: a released prefix signals the region is
///    committed/consumed, and the producer advances its append/compaction cursor
///    in response.
///
/// Implementing this trait is a deliberate statement that the producer obeys the
/// contract above. Invariant (2)'s position-stability is maintained *by
/// construction* (the engine/window appends immutable positions and only
/// compacts released prefixes); [`Self::debug_assert_position_invariant`] does
/// not re-derive it. It cheaply checks the producer's own append/compaction
/// **bookkeeping** — the per-cursor/per-writer state whose desync is how a
/// compaction or wiring bug would actually manifest — in debug builds.
pub(crate) trait CyclicSequencingProducer: TileProducer {
    /// Debug-only check of the append/compaction bookkeeping backing the
    /// append-only / position-stable invariant (contract item 2), called from
    /// the producer's `get` path — e.g. that per-writer cursors stay aligned
    /// with the writer set. A failure is a compaction or wiring bug, not a user
    /// error; a no-op in release builds.
    fn debug_assert_position_invariant(&self);
}

/// Represents a step on a path through a Tile structure
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TilePathStep {
    /// A step into a specific field of a Record
    Record(String),
    /// A step into the codomain of a function
    Codomain,
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::{InspectNode, ProducerBase, Tile, TileGuard, TileProducer, Tiling, VizOptions};

    /// A test helper TileProducer that returns a pre-determined tile.
    /// Useful for testing TileOperators by injecting tiles directly.
    pub(crate) struct TestTileProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
    }

    impl TestTileProducer {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> Self {
            Self {
                base: ProducerBase::new(Self::alloc_id(), &tiling),
                tile,
            }
        }
    }

    /// A [`TileProducer`] that answers each pull with whatever tile its shared cell holds,
    /// so a test can change its input between pulls. What a producer states on one pull
    /// constrains what it may answer on the next (`src/interpreter/design-operators.md`,
    /// "The completeness contract"), which a fixed tile cannot exercise.
    pub(crate) struct ScriptedProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: std::rc::Rc<std::cell::RefCell<Tile>>,
    }

    impl ScriptedProducer {
        /// The producer, and the cell a test writes the next pull's answer into.
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::rc::Rc<std::cell::RefCell<Tile>>) {
            let cell = std::rc::Rc::new(std::cell::RefCell::new(tile));
            let producer = Self {
                base: ProducerBase::new(Self::alloc_id(), &tiling),
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

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.borrow().clone()
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// A value in a record's field filled in beneath a key already called complete is an
    /// addition beneath a complete path, which the completeness contract forbids.
    #[test]
    #[should_panic(expected = "beneath a path it had called complete")]
    fn a_record_field_filled_beneath_a_complete_key_is_reported() {
        use crate::interpreter::{ColumnValue, Predicate};
        use bit_set::BitSet;
        use std::collections::HashMap;
        let with_n = |n: ColumnValue| {
            // Built directly rather than through `Tile::data_function`, which a tile holding
            // a complete key with an empty field need not pass: this is the check's input.
            Tile::DataFunction {
                row_starts: ColumnValue::UInts(vec![0]),
                domain: ColumnValue::UInts(vec![0]),
                codomain: Box::new(Tile::Record(HashMap::from([
                    ("n".to_string(), Tile::Scalar(n)),
                    (
                        "xs".to_string(),
                        Tile::grouped(
                            ColumnValue::UInts(vec![0]),
                            ColumnValue::UInts(vec![]),
                            Box::new(Tile::Scalar(ColumnValue::UInts(vec![]))),
                            Predicate::False,
                            BitSet::new(),
                        ),
                    ),
                ]))),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
            }
        };
        let last = with_n(ColumnValue::Ints(vec![]));
        let result = with_n(ColumnValue::Ints(vec![5]));
        super::assert_complete_region_unchanged(
            "a_record_field",
            &last,
            &result,
            &TileGuard::Function(super::FunctionGuard::Domain(Predicate::False)),
        );
    }

    /// A [`TileProducer`] that answers with a fixed tile and records every release
    /// guard it is handed, for asserting that a release *propagates*.
    pub(crate) struct ReleaseSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        pub(crate) released: std::rc::Rc<std::cell::RefCell<Vec<TileGuard>>>,
    }

    impl ReleaseSpy {
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::rc::Rc<std::cell::RefCell<Vec<TileGuard>>>) {
            let released = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::new(Self::alloc_id(), &tiling),
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

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.borrow_mut().push(obsolete_guard);
        }
    }

    impl TileProducer for TestTileProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
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
        pub(crate) released: std::rc::Rc<std::cell::RefCell<Vec<TileGuard>>>,
    }

    impl QuietSpy {
        pub(crate) fn new(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, std::rc::Rc<std::cell::RefCell<Vec<TileGuard>>>) {
            let released = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::new(Self::alloc_id(), &tiling),
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

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            let mut tile = self.tile.clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            tile
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.borrow_mut().push(obsolete_guard);
        }
    }
}
