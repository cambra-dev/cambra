//! The static structure of the dataflow operator graph.
//!
//! The graph is built by walking the operators from the program's outputs, in
//! [`BoundarySession::into_graph`]. Each operator states what it holds through
//! [`TileOperator::visit_inputs`], which is the single statement of its inputs:
//! the walk reads it, and so does `TileOperator::inspect`, which renders an
//! operator's children from the same answer.
//!
//! The walk runs between conversion and the subscribe loop, which is the only
//! window in which it is total. `subscribe` takes every [`CycleSlot`] and every
//! store's `init_ops`, so an operator asked for its inputs after that answers
//! without them.
//!
//! An edge is a **subscription**: the consumer holds the operator the edge names
//! and calls `get` on it. `notify` runs the other way along the same edges, so an
//! edge is the pull direction rather than dataflow as a whole. Two edges are held
//! without being subscribed — a read of a data source, which is not an operator,
//! and a fan branch that lost `should_subscribe` while its sibling drove the
//! subscribe for all of them.
//!
//! Degrees are counted in dataflow direction — a source has in-degree 0, a sink
//! out-degree 0 — while an edge is stored on the consumer and names the node it
//! subscribes, so the stored relation runs the other way.
//!
//! What the walk cannot produce is the two boundary node kinds. A source and a
//! sink are graph nodes rather than operators, so neither has an identity to read
//! off an operator, and a source's provenance row names every expression that
//! reads it — which conversion knows and the walk does not. Conversion records
//! that much and nothing else; see [`Boundaries`].
//!
//! `src/interpreter/design-operators.md`, "Operator identity and the graph the
//! inspector reads" owns the design.
//!
//! [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
//! [`TileOperator::visit_inputs`]: crate::interpreter::tile_operators::TileOperator::visit_inputs

use std::cell::RefCell;

use crate::ccl::provenance::NodeId;
use crate::interpreter::tile_operators::TileOperator;
use crate::interpreter::tiling::Tiling;

/// How a downstream operator holds one of its inputs.
///
/// Exhaustive over the operator-to-operator edges the production operators have,
/// measured from their fields. The plan note under
/// `projects/program-inspector` in the internal vault carries the survey.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    /// An exclusively owned `Box<dyn TileOperator>`.
    ///
    /// `deferred` marks one wired through a [`CycleSlot`] after the owner was
    /// constructed, which is an attribute of *when* rather than of ownership:
    /// every ownership question answers the same as an ordinary `Box`.
    ///
    /// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
    Value { deferred: bool },
    /// An edge to a node more than one consumer may reach: a `FanOutBranch`'s
    /// edge to its fan input, or a reader's edge to a data source.
    ///
    /// What separates this from [`Value`](Self::Value) is exclusivity, not
    /// indirection. A node several consumers subscribe has no single owner,
    /// which is why the forest invariant ranges over value edges alone.
    Share,
}

/// What names an input at its consumer.
///
/// Three shapes, because operator arity is not uniform: a named field, a position
/// in a `Vec`, or a store key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgeRole {
    /// The field the consumer stores the input under, e.g. `"input"`,
    /// `"predicate"`, `"default"`.
    Named(&'static str),
    /// A position in a `Vec` of inputs, as `FanIn` and `UnionOperator` have.
    Positional(usize),
    /// A store key, as both stores' `init_ops` are keyed by.
    StoreKey(String),
}

/// How a role reads as a label — the same rendering the wire's
/// `OperatorEdgeRole` ships, and what `inspect` names a child by.
impl std::fmt::Display for EdgeRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EdgeRole::Named(name) => f.write_str(name),
            EdgeRole::Positional(index) => write!(f, "{index}"),
            EdgeRole::StoreKey(key) => f.write_str(key),
        }
    }
}

/// One recorded input edge.
#[derive(Clone, Debug)]
pub struct InputEdge {
    pub(crate) role: EdgeRole,
    pub(crate) kind: EdgeKind,
    pub(crate) subscribed: NodeId,
}

/// What an input edge points at.
///
/// A source is the one target that is not an operator, so it is the one target a
/// walk stops at rather than descends into.
pub enum InputTarget<'a> {
    /// Another operator.
    Operator(&'a dyn TileOperator),
    /// A registered data source, under the name it was registered with.
    Source(&'a str),
}

/// One input edge, as the operator holding it states it.
pub struct InputEdgeSpec<'a> {
    pub(crate) role: EdgeRole,
    pub(crate) kind: EdgeKind,
    pub(crate) target: InputTarget<'a>,
}

/// An owned input held under a named field.
pub(crate) fn value<'a>(role: &'static str, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Named(role),
        kind: EdgeKind::Value { deferred: false },
        target: InputTarget::Operator(op),
    }
}

/// An owned input at a position in a `Vec`.
pub(crate) fn value_at<'a>(index: usize, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Positional(index),
        kind: EdgeKind::Value { deferred: false },
        target: InputTarget::Operator(op),
    }
}

/// An owned input keyed by a store key, as both stores' `init_ops` are.
pub(crate) fn value_keyed<'a>(
    key: impl Into<String>,
    op: &'a dyn TileOperator,
) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::StoreKey(key.into()),
        kind: EdgeKind::Value { deferred: false },
        target: InputTarget::Operator(op),
    }
}

/// An owned input wired through a [`CycleSlot`] after its holder was built.
///
/// Deferred is a property of the field rather than of the run: a slot is the only
/// way an operator receives an input it did not get from its constructor, so
/// every slot-held input is deferred and no other input is.
///
/// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
pub(crate) fn value_late<'a>(role: EdgeRole, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role,
        kind: EdgeKind::Value { deferred: true },
        target: InputTarget::Operator(op),
    }
}

/// A branch's edge to its fan input.
///
/// Whether the fan closes a cycle is not this edge's business. Every cycle in
/// the graph runs through an input wired late — see [`EdgeKind::Value`]'s
/// `deferred` — and a store's remaining branches serve its downstream reads.
pub(crate) fn share<'a>(fan_input: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Named("fan"),
        kind: EdgeKind::Share,
        target: InputTarget::Operator(fan_input),
    }
}

/// A read of a registered data source.
///
/// Shared, not owned: one registered source may be read by several expressions,
/// and each reader holds it through an `Rc` the way a fan branch holds its fan.
pub(crate) fn source(name: &str) -> InputEdgeSpec<'_> {
    InputEdgeSpec {
        role: EdgeRole::Named("source"),
        kind: EdgeKind::Share,
        target: InputTarget::Source(name),
    }
}

/// One node of the graph.
///
/// Operators, plus the two program-boundary kinds. Without the boundary the graph
/// begins and ends in the middle of nothing: a data source is not an operator, and
/// an output is a field name the boundary holds rather than an operator itself.
#[derive(Clone, Debug)]
pub enum GraphNode {
    /// An operator, with the inputs it holds.
    Operator {
        id: NodeId,
        kind: &'static str,
        tiling: Tiling,
        inputs: Vec<InputEdge>,
    },
    /// A registered data source. In-degree 0, and where a path through the graph
    /// starts.
    ///
    /// One per registered source rather than one per read site, so the graph is
    /// truthful about sharing the way it is everywhere else — a shared input is a
    /// node several consumers point at, never a node duplicated per consumer.
    Source { id: NodeId, name: String },
    /// A compiled output field. Out-degree 0, and a start of every walk.
    Sink {
        id: NodeId,
        name: String,
        input: InputEdge,
    },
}

/// The static operator graph of one compiled program.
///
/// Sources first, then each output's operators with a holder after everything it
/// holds, then that output's sink. Deterministic: the walk visits an operator's
/// inputs in the order the operator states them.
#[derive(Clone, Debug, Default)]
pub struct OperatorGraph {
    nodes: Vec<GraphNode>,
}

impl OperatorGraph {
    /// Every node, in walk order.
    pub fn nodes(&self) -> &[GraphNode] {
        &self.nodes
    }

    /// The nodes no `Value` edge subscribes, which is where a walk of the
    /// subscription forest starts.
    ///
    /// Derived from the edges rather than recorded. A node's owner is the one
    /// `Value` edge that names it, so the edge table already answers this and a
    /// stored copy could only disagree with it.
    ///
    /// Three kinds of node qualify. A **sink**: nothing subscribes it. A **fan
    /// input**: the `Rc<FanOut>` holding it is dropped when conversion ends, so
    /// only its branches survive, and each names it with a `Share` — and a
    /// binding whose variable is never used has a fan with no branches at all,
    /// so nothing names it. A **source**: a source is a graph node rather than a
    /// `TileOperator`, so nothing subscribes it and a reader's edge to it is a
    /// `Share`.
    ///
    /// Every node of the graph is reachable from here along `Value` edges alone,
    /// which is what [`assert_graph_invariants`] pins.
    pub(crate) fn walk_starts(&self) -> Vec<NodeId> {
        let owned: std::collections::HashSet<NodeId> = self
            .edges()
            .filter(|(_, e)| matches!(e.kind, EdgeKind::Value { .. }))
            .map(|(_, e)| e.subscribed)
            .collect();
        self.ids().filter(|id| !owned.contains(id)).collect()
    }

    /// Every node's id.
    pub(crate) fn ids(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes.iter().map(|n| match n {
            GraphNode::Operator { id, .. }
            | GraphNode::Source { id, .. }
            | GraphNode::Sink { id, .. } => *id,
        })
    }

    /// Every edge, as `(consumer, edge)`.
    pub(crate) fn edges(&self) -> impl Iterator<Item = (NodeId, &InputEdge)> + '_ {
        self.nodes
            .iter()
            .flat_map(|n| -> Box<dyn Iterator<Item = _>> {
                match n {
                    GraphNode::Operator { id, inputs, .. } => {
                        Box::new(inputs.iter().map(move |e| (*id, e)))
                    }
                    GraphNode::Sink { id, input, .. } => Box::new(std::iter::once((*id, input))),
                    GraphNode::Source { .. } => Box::new(std::iter::empty()),
                }
            })
    }
}

/// Assert the graph's structural invariants, at the conversion boundary.
///
/// Gated as an expression rather than a `#[cfg]` item, mirroring
/// [`assert_unique_node_ids`](crate::ccl::context::assert_unique_node_ids), so
/// the same call site compiles under every clippy pass.
///
/// Two invariants, neither type-enforced:
///
/// * **The value edges form a forest.** Ownership is single because every owned
///   input is a `Box`. Acyclicity follows from the other two assertions rather
///   than standing on its own: a value cycle's members each have their only
///   value parent inside the cycle, so none is a walk start and no value edge
///   enters from outside, which the reachability check reports as stranded. The
///   renderer's absence of a cycle guard rests on this.
/// * **Every node is reachable from [`OperatorGraph::walk_starts`] along the `Value`
///   edges.** That relation is the one every consumer walks — the renderer draws
///   value edges as the child relation and share edges as reference leaves — so a
///   node it misses is a node nothing draws. An unreachable node is one a
///   construction site built and dropped, which nothing else notices.
pub(crate) fn assert_graph_invariants(graph: &OperatorGraph) {
    if !cfg!(any(debug_assertions, test)) {
        return;
    }
    let ids: std::collections::HashSet<NodeId> = graph.ids().collect();

    let mut value_parent: std::collections::HashMap<NodeId, NodeId> =
        std::collections::HashMap::new();
    for (consumer, edge) in graph.edges() {
        assert!(
            ids.contains(&edge.subscribed),
            "operator graph: an edge from {consumer:?} points at {:?}, which is no node of \
             the graph",
            edge.subscribed
        );
        if matches!(edge.kind, EdgeKind::Value { .. }) {
            let previous = value_parent.insert(edge.subscribed, consumer);
            assert!(
                previous.is_none(),
                "operator graph: {:?} is owned by both {previous:?} and {consumer:?}, but a \
                 value edge is exclusive ownership",
                edge.subscribed
            );
        }
    }

    // `Value` edges only, from `walk_starts`: that is the relation a consumer walks,
    // and every node nothing owns — a sink, a fan input, a source — is in
    // `walk_starts` already, so no share edge has to be followed to reach one.
    let mut seen: std::collections::HashSet<NodeId> = std::collections::HashSet::new();
    let mut stack: Vec<NodeId> = graph.walk_starts();
    let by_id: std::collections::HashMap<NodeId, &GraphNode> = graph
        .nodes()
        .iter()
        .map(|n| match n {
            GraphNode::Operator { id, .. }
            | GraphNode::Source { id, .. }
            | GraphNode::Sink { id, .. } => (*id, n),
        })
        .collect();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        match by_id.get(&id) {
            Some(GraphNode::Operator { inputs, .. }) => {
                stack.extend(
                    inputs
                        .iter()
                        .filter(|e| matches!(e.kind, EdgeKind::Value { .. }))
                        .map(|e| e.subscribed),
                );
            }
            Some(GraphNode::Sink { input, .. }) => stack.push(input.subscribed),
            Some(GraphNode::Source { .. }) | None => {}
        }
    }
    let stranded: Vec<String> = ids
        .difference(&seen)
        .map(|id| match by_id.get(id) {
            Some(GraphNode::Operator { kind, tiling, .. }) => format!("{id:?} {kind} {tiling}"),
            Some(GraphNode::Source { name, .. }) => format!("{id:?} Source({name})"),
            Some(GraphNode::Sink { name, .. }) => format!("{id:?} Sink({name})"),
            None => format!("{id:?} <no node>"),
        })
        .collect();
    assert!(
        stranded.is_empty(),
        "operator graph: {} node(s) unreachable from `walk_starts` along the value edges — a \
         construction site built an operator and dropped it: {stranded:?}",
        stranded.len()
    );
}

// The program's boundary nodes, live only while a `BoundarySession` is installed.
//
// shared-state-ok: a recorder, mirroring `provenance::ACTIVE_TABLE`. What crosses
// it is boundary identity, never a value passed between operators.
thread_local! {
    // shared-state-ok: the recorder cell itself, for the reason on the macro
    // above. The declaration matches the checker's ambient-state shape twice —
    // once at the macro, once at the `static` — and its upward scan stops at
    // `thread_local! {`, which is neither a comment nor an attribute, so the
    // note above does not reach this line.
    static BOUNDARIES: RefCell<Option<Boundaries>> = const { RefCell::new(None) };
}

/// The program's boundary nodes, which no walk of the operators can produce.
///
/// A source and a sink are graph nodes rather than operators, so neither has an
/// identity or a provenance row that a walk could read off an operator. A
/// source's row names every expression that reads it, which only conversion
/// knows: the walk sees reader operators, not the expressions they came from.
///
/// Everything else comes from the walk — every operator, and every edge,
/// including the edges into these nodes.
#[derive(Default)]
struct Boundaries {
    /// The expressions that read each registered source, in first-read order.
    source_reads: Vec<(String, Vec<NodeId>)>,
    /// Each read source's node, once [`materialize_sources`] has minted it.
    sources: Vec<(String, NodeId)>,
    /// Each compiled output field's node.
    sinks: Vec<(String, NodeId)>,
}

/// RAII installer for the per-compile boundary record.
///
/// A session is needed because the recording points are inside operator
/// conversion, which takes no context parameter for this.
#[must_use = "a dropped BoundarySession takes the boundaries with it — bind it and call `into_graph`"]
pub(crate) struct BoundarySession;

impl BoundarySession {
    /// Install a fresh boundary record for the extent of this value.
    pub(crate) fn install() -> Self {
        BOUNDARIES.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a boundary session is already installed; sessions are per-compile and \
                 do not nest"
            );
            *slot = Some(Boundaries::default());
        });
        BoundarySession
    }

    /// Walk `outputs` into the graph, ending the session.
    ///
    /// Runs before `subscribe`, which is what makes the walk total: `subscribe`
    /// takes every [`CycleSlot`] and every store's `init_ops`, so an operator
    /// asked for its inputs afterwards would answer without them.
    ///
    /// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
    pub(crate) fn into_graph(self, outputs: &[(String, Box<dyn TileOperator>)]) -> OperatorGraph {
        let boundaries = BOUNDARIES
            .with(|slot| slot.borrow_mut().take())
            .unwrap_or_default();
        let mut nodes = Vec::new();
        let mut seen = std::collections::HashSet::new();

        for (name, id) in &boundaries.sources {
            nodes.push(GraphNode::Source {
                id: *id,
                name: name.clone(),
            });
        }
        for (name, op) in outputs {
            walk_operator(&**op, &boundaries, &mut seen, &mut nodes);
            let (Some(id), Some(subscribed)) = (
                boundaries
                    .sinks
                    .iter()
                    .find(|(n, _)| n == name)
                    .map(|(_, id)| *id),
                op.operator_id(),
            ) else {
                continue;
            };
            nodes.push(GraphNode::Sink {
                id,
                name: name.clone(),
                input: InputEdge {
                    role: EdgeRole::Named("output"),
                    kind: EdgeKind::Value { deferred: false },
                    subscribed,
                },
            });
        }
        OperatorGraph { nodes }
    }
}

impl Drop for BoundarySession {
    fn drop(&mut self) {
        BOUNDARIES.with(|slot| *slot.borrow_mut() = None);
    }
}

/// Emit `op` and everything it holds, children before their holder.
///
/// An operator answering no id is a test double, which the walk neither emits
/// nor descends into — nothing installs a session around a test that builds
/// operators by hand.
fn walk_operator(
    op: &dyn TileOperator,
    boundaries: &Boundaries,
    seen: &mut std::collections::HashSet<NodeId>,
    nodes: &mut Vec<GraphNode>,
) {
    let Some(id) = op.operator_id() else {
        return;
    };
    if !seen.insert(id) {
        return;
    }
    let mut inputs = Vec::new();
    op.visit_inputs(&mut |spec| {
        let subscribed = match spec.target {
            InputTarget::Operator(child) => {
                walk_operator(child, boundaries, seen, nodes);
                match child.operator_id() {
                    Some(child_id) => child_id,
                    None => return,
                }
            }
            InputTarget::Source(name) => match boundaries.sources.iter().find(|(n, _)| n == name) {
                Some((_, source_id)) => *source_id,
                None => {
                    debug_assert!(
                        false,
                        "operator graph: {name:?} is read but was never recorded as a \
                             source, so its node was never minted"
                    );
                    return;
                }
            },
        };
        inputs.push(InputEdge {
            role: spec.role,
            kind: spec.kind,
            subscribed,
        });
    });
    nodes.push(GraphNode::Operator {
        id,
        kind: op.kind(),
        tiling: op.tiling().clone(),
        inputs,
    });
}

/// Note that the expression `expr` reads the source registered under `name`.
///
/// The node itself is minted later, by [`materialize_sources`]: its row names
/// every site that reads it, and a row's parents are fixed when its recording
/// closes.
pub(crate) fn record_source_read(name: &str, expr: NodeId) {
    BOUNDARIES.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(boundaries) = slot.as_mut() else {
            return;
        };
        match boundaries.source_reads.iter_mut().find(|(n, _)| n == name) {
            Some((_, reads)) => reads.push(expr),
            None => boundaries.source_reads.push((name.to_string(), vec![expr])),
        }
    });
}

/// Mint one node per registered source that something read.
///
/// Must run inside the conversion phase scope, since each node needs a provenance
/// row like any other node of the pane. Each row names every read site: the first
/// through the recording, the rest through
/// [`RecordingGuard::also_consumes`](crate::ccl::provenance::RecordingGuard::also_consumes),
/// which is what a node consumed from several places is for.
pub(crate) fn materialize_sources() {
    let pending = BOUNDARIES.with(|slot| {
        slot.borrow_mut()
            .as_mut()
            .map(|b| std::mem::take(&mut b.source_reads))
            .unwrap_or_default()
    });
    for (name, reads) in pending {
        let Some(first) = reads.first() else {
            continue;
        };
        let id = {
            let guard = crate::ccl::provenance::enter(
                *first,
                "opconv.source",
                crate::ccl::provenance::Nature::Machinery,
            );
            for extra in &reads[1..] {
                guard.also_consumes(*extra);
            }
            let id = NodeId::fresh();
            crate::ccl::provenance::on_mint(id);
            id
        };
        BOUNDARIES.with(|slot| {
            if let Some(boundaries) = slot.borrow_mut().as_mut() {
                boundaries.sources.push((name, id));
            }
        });
    }
}

/// Mint the node for a compiled output field.
pub(crate) fn record_sink(name: &str) {
    let id = NodeId::fresh();
    crate::ccl::provenance::on_mint(id);
    BOUNDARIES.with(|slot| {
        if let Some(boundaries) = slot.borrow_mut().as_mut() {
            boundaries.sinks.push((name.to_string(), id));
        }
    });
}
