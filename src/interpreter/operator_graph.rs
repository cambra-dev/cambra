//! The static structure of the dataflow operator graph, captured as it is built.
//!
//! The graph is recorded rather than walked, for two reasons that are facts about
//! the operators rather than choices:
//!
//! * **An edge's kind is not recoverable from the operator.** [`FanOut::branch`]
//!   returns a `Box<dyn TileOperator>` and `FanOutBranch` is private, so a shared
//!   input's field type is identical to an owned one. Whether a fan is cyclic
//!   lives in `FanOutShared`, which a branch exposes no accessor for.
//! * **A `CycleSlot`'s only accessor consumes it.** `subscribe` calls `take`, and
//!   `compile_program` subscribes before it returns, so a walk of a finished
//!   `CompiledProgram` has already lost the commit store's writers and the
//!   induction store's body.
//!
//! So the recording happens at construction, through [`OperatorBase::new`], and
//! accumulates into a thread-local [`GraphSession`] that `compile_program`
//! installs around conversion. Outside a session every record is a no-op, which
//! is what keeps the operator constructions in engine tests from accumulating.
//!
//! What the edges mean: they are **construction** edges — which operator holds
//! which, and how. Runtime dataflow follows `get` and `notify`, which is a
//! different relation, and nothing here asserts the two coincide.
//!
//! [`FanOut::branch`]: crate::interpreter::tile_operators::FanOut::branch
//! [`OperatorBase::new`]: crate::interpreter::tile_operators::OperatorBase::new

use std::cell::RefCell;

use crate::ccl::provenance::NodeId;
use crate::interpreter::tile_operators::TileOperator;

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
    /// indirection. A shared target has no single owner, which is why the forest
    /// invariant ranges over value edges alone.
    Share,
    /// A `FanOutBranch`'s edge to the fan input of a cyclic fan. Every cycle in
    /// the graph is one of these, which is what makes the cycle set explicit and
    /// lets the value edges stay a forest.
    Feedback,
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

/// One recorded input edge.
#[derive(Clone, Debug)]
pub struct InputEdge {
    pub role: EdgeRole,
    pub kind: EdgeKind,
    pub target: NodeId,
}

/// An input edge as a constructor states it, before the session resolves it.
///
/// `target` is an `Option` because a test double carries no [`OperatorBase`] and
/// so answers no id. Such an edge is dropped rather than recorded: a graph is
/// only ever assembled under a session, and nothing installs one around a test
/// that builds operators by hand.
///
/// [`OperatorBase`]: crate::interpreter::tile_operators::OperatorBase
pub struct InputEdgeSpec {
    pub role: EdgeRole,
    pub kind: EdgeKind,
    pub target: Option<NodeId>,
}

/// An owned input held under a named field.
pub(crate) fn value(role: &'static str, op: &dyn TileOperator) -> InputEdgeSpec {
    InputEdgeSpec {
        role: EdgeRole::Named(role),
        kind: EdgeKind::Value { deferred: false },
        target: op.operator_id(),
    }
}

/// An owned input at a position in a `Vec`.
pub(crate) fn value_at(index: usize, op: &dyn TileOperator) -> InputEdgeSpec {
    InputEdgeSpec {
        role: EdgeRole::Positional(index),
        kind: EdgeKind::Value { deferred: false },
        target: op.operator_id(),
    }
}

/// An owned input keyed by a store key, as both stores' `init_ops` are.
pub(crate) fn value_keyed(key: impl Into<String>, op: &dyn TileOperator) -> InputEdgeSpec {
    InputEdgeSpec {
        role: EdgeRole::StoreKey(key.into()),
        kind: EdgeKind::Value { deferred: false },
        target: op.operator_id(),
    }
}

/// A branch's edge to its fan input, `Feedback` when the fan is cyclic.
pub(crate) fn share(fan_input: Option<NodeId>, cyclic: bool) -> InputEdgeSpec {
    InputEdgeSpec {
        role: EdgeRole::Named("fan"),
        kind: if cyclic {
            EdgeKind::Feedback
        } else {
            EdgeKind::Share
        },
        target: fan_input,
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
        tiling: String,
        inputs: Vec<InputEdge>,
    },
    /// A registered data source. In-degree 0, and where a path through the graph
    /// starts.
    ///
    /// One per registered source rather than one per read site, so the graph is
    /// truthful about sharing the way it is everywhere else — a shared input is a
    /// node several consumers point at, never a node duplicated per consumer.
    Source { id: NodeId, name: String },
    /// A compiled output field. Out-degree 0, and a root of every walk.
    Sink {
        id: NodeId,
        name: String,
        input: InputEdge,
    },
}

/// The static operator graph of one compiled program.
///
/// Nodes are in conversion order, which is deterministic: no construction loop
/// iterates a `HashMap`.
#[derive(Clone, Debug, Default)]
pub struct OperatorGraph {
    nodes: Vec<GraphNode>,
    roots: Vec<NodeId>,
    /// Read sites per registered source, accumulated during the walk and spent by
    /// [`materialize_sources`].
    ///
    /// A source node cannot be minted at the first read site: its row names every
    /// site that reads it, and a row's parents are fixed when its recording
    /// closes. So the sites are collected and the node minted once the walk is
    /// done.
    pending_sources: Vec<(String, Vec<SourceRead>)>,
}

/// One read of a registered data source: the expression that read it, and the
/// operator that read reached.
#[derive(Clone, Copy, Debug)]
struct SourceRead {
    expr: NodeId,
    reader: NodeId,
}

impl OperatorGraph {
    /// Every node, in conversion order.
    pub fn nodes(&self) -> &[GraphNode] {
        &self.nodes
    }

    /// The nodes no operator owns, which is where a walk of the graph starts.
    ///
    /// A fan input is one: the `Rc<FanOut>` holding it is dropped when conversion
    /// ends, so only its branches survive and nothing owns the input itself. A
    /// binding whose variable is never used has a fan with no branches at all, so
    /// its input is reached by no edge either.
    ///
    /// The program outputs are the other roots, and the boundary supplies those —
    /// only the caller knows which operators it compiled a field to.
    pub fn roots(&self) -> &[NodeId] {
        &self.roots
    }

    /// Every node's id.
    pub fn ids(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes.iter().map(|n| match n {
            GraphNode::Operator { id, .. }
            | GraphNode::Source { id, .. }
            | GraphNode::Sink { id, .. } => *id,
        })
    }

    /// Every edge, as `(consumer, edge)`.
    pub fn edges(&self) -> impl Iterator<Item = (NodeId, &InputEdge)> + '_ {
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
///   input is a `Box`, and acyclicity comes from cycles routing through the two
///   cyclic fans rather than through owned inputs. The renderer's absence of a
///   cycle guard rests on this.
/// * **Every node is reachable from a root** — a sink, or a fan input, which are
///   the two kinds of node nothing owns. An unreachable node is one a
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
            ids.contains(&edge.target),
            "operator graph: an edge from {consumer:?} points at {:?}, which is no node of \
             the graph",
            edge.target
        );
        if matches!(edge.kind, EdgeKind::Value { .. }) {
            let previous = value_parent.insert(edge.target, consumer);
            assert!(
                previous.is_none(),
                "operator graph: {:?} is owned by both {previous:?} and {consumer:?}, but a \
                 value edge is exclusive ownership",
                edge.target
            );
        }
    }

    // Reachability follows every edge kind: a fan input is reached through its
    // branches' share edges, not by being owned.
    let mut seen: std::collections::HashSet<NodeId> = std::collections::HashSet::new();
    let mut stack: Vec<NodeId> = graph.roots().to_vec();
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
                stack.extend(inputs.iter().map(|e| e.target));
            }
            Some(GraphNode::Sink { input, .. }) => stack.push(input.target),
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
        "operator graph: {} node(s) unreachable from any output — a construction site \
         built an operator and dropped it: {stranded:?}",
        stranded.len()
    );
}

// The accumulating graph, live only while a `GraphSession` is installed.
//
// shared-state-ok: a recorder, mirroring `provenance::ACTIVE_TABLE`. What crosses
// it is graph structure, never a value passed between operators.
thread_local! {
    // shared-state-ok: the recorder cell itself, for the reason on the macro
    // above. The declaration matches the checker's ambient-state shape twice —
    // once at the macro, once at the `static` — and its upward scan stops at
    // `thread_local! {`, which is neither a comment nor an attribute, so the
    // note above does not reach this line.
    static ACTIVE_GRAPH: RefCell<Option<OperatorGraph>> = const { RefCell::new(None) };
}

/// RAII installer for the per-compile [`OperatorGraph`].
///
/// A session is needed because [`OperatorBase::new`] is called from inside
/// operator constructors, which take no context parameter — threading one would
/// change every constructor call site, including the ones in tests, which is the
/// cost this design exists to avoid.
///
/// [`OperatorBase::new`]: crate::interpreter::tile_operators::OperatorBase::new
#[must_use = "a dropped GraphSession takes the graph with it — bind it and call `into_graph`"]
pub(crate) struct GraphSession;

impl GraphSession {
    /// Install a fresh graph for the extent of this value.
    pub(crate) fn install() -> Self {
        ACTIVE_GRAPH.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a graph session is already installed; sessions are per-compile and \
                 do not nest"
            );
            *slot = Some(OperatorGraph::default());
        });
        GraphSession
    }

    /// Take the accumulated graph, ending the session.
    pub(crate) fn into_graph(self) -> OperatorGraph {
        ACTIVE_GRAPH
            .with(|slot| slot.borrow_mut().take())
            .unwrap_or_default()
    }
}

impl Drop for GraphSession {
    fn drop(&mut self) {
        ACTIVE_GRAPH.with(|slot| *slot.borrow_mut() = None);
    }
}

/// Record an operator and the inputs it holds.
///
/// A no-op with no session installed, which is every engine test that builds an
/// operator by hand.
pub(crate) fn record_operator(
    id: NodeId,
    kind: &'static str,
    tiling: &crate::interpreter::tiling::Tiling,
    inputs: &[InputEdgeSpec],
) {
    ACTIVE_GRAPH.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(graph) = slot.as_mut() else {
            return;
        };
        graph.nodes.push(GraphNode::Operator {
            id,
            kind,
            tiling: tiling.to_string(),
            inputs: resolve(inputs),
        });
    });
}

/// Note that `reader` reads the source registered under `name`, at expression
/// `expr`.
///
/// The node itself is minted later, by [`materialize_sources`]; see
/// [`OperatorGraph::pending_sources`].
pub(crate) fn record_source_read(name: &str, expr: NodeId, reader: Option<NodeId>) {
    let Some(reader) = reader else {
        return;
    };
    ACTIVE_GRAPH.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(graph) = slot.as_mut() else {
            return;
        };
        let read = SourceRead { expr, reader };
        match graph.pending_sources.iter_mut().find(|(n, _)| n == name) {
            Some((_, reads)) => reads.push(read),
            None => graph.pending_sources.push((name.to_string(), vec![read])),
        }
    });
}

/// Mint one source node per registered source, and the edge from every operator
/// that reads it.
///
/// Must run inside the conversion phase scope, since each node needs a provenance
/// row like any other node of the pane. Each row names every read site: the first
/// through the recording, the rest through
/// [`RecordingGuard::also_consumes`](crate::ccl::provenance::RecordingGuard::also_consumes),
/// which is what a node consumed from several places is for.
pub(crate) fn materialize_sources() {
    let pending = ACTIVE_GRAPH.with(|slot| {
        slot.borrow_mut()
            .as_mut()
            .map(|graph| std::mem::take(&mut graph.pending_sources))
            .unwrap_or_default()
    });
    for (name, reads) in pending {
        let Some(first) = reads.first() else {
            continue;
        };
        let id = {
            let guard = crate::ccl::provenance::enter(
                first.expr,
                "opconv.source",
                crate::ccl::provenance::Nature::Machinery,
            );
            let rest: Vec<NodeId> = reads[1..].iter().map(|r| r.expr).collect();
            for extra in &rest {
                guard.also_consumes(*extra);
            }
            let id = NodeId::fresh();
            crate::ccl::provenance::on_mint(id);
            id
        };
        ACTIVE_GRAPH.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(graph) = slot.as_mut() else {
                return;
            };
            graph.nodes.push(GraphNode::Source {
                id,
                name: name.clone(),
            });
            for read in &reads {
                // Shared, not owned: one registered source may be read by
                // several expressions, and each reader holds it through an `Rc`
                // the way a fan branch holds its fan.
                push_edge(
                    graph,
                    read.reader,
                    EdgeRole::Named("source"),
                    EdgeKind::Share,
                    id,
                );
            }
        });
    }
}

/// Record a compiled output field, reading `target`.
pub(crate) fn record_sink(name: &str, target: Option<NodeId>) -> Option<NodeId> {
    let target = target?;
    let id = NodeId::fresh();
    crate::ccl::provenance::on_mint(id);
    ACTIVE_GRAPH.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(graph) = slot.as_mut() else {
            return;
        };
        graph.nodes.push(GraphNode::Sink {
            id,
            name: name.to_string(),
            input: InputEdge {
                role: EdgeRole::Named("output"),
                kind: EdgeKind::Value { deferred: false },
                target,
            },
        });
        graph.roots.push(id);
    });
    Some(id)
}

/// Remove an operator a conversion arm built and then discarded.
///
/// Not a correctness fix: the discarded operator is unreachable, so nothing ever
/// subscribes it and at runtime it does not exist. What it would leave behind is
/// a phantom node in the graph — a node the pane renders leading nowhere, which
/// a reader has no way to tell from a real operator whose consumer is missing.
/// Dropping it here keeps the graph to operators the program actually has.
///
/// The provenance row the mint wrote is left alone. Its key is no longer a node
/// of the pane, so the fold reads it as a transient born and consumed inside the
/// phase and composes it away, which is what it is.
pub(crate) fn drop_operator(op: &dyn TileOperator) {
    let Some(id) = op.operator_id() else {
        return;
    };
    ACTIVE_GRAPH.with(|slot| {
        if let Some(graph) = slot.borrow_mut().as_mut() {
            graph.nodes.retain(|n| match n {
                GraphNode::Operator { id: node, .. } => *node != id,
                GraphNode::Source { .. } | GraphNode::Sink { .. } => true,
            });
            graph.roots.retain(|root| *root != id);
        }
    });
}

/// Record a fan input as a root.
///
/// Called by `FanOut`'s constructor, which is the only place that knows an
/// operator has been moved into a fan and so is owned by no operator.
pub(crate) fn record_fan_input(id: Option<NodeId>) {
    let Some(id) = id else {
        return;
    };
    ACTIVE_GRAPH.with(|slot| {
        if let Some(graph) = slot.borrow_mut().as_mut() {
            graph.roots.push(id);
        }
    });
}

/// Record an edge onto an operator already in the graph.
///
/// The deferred half of the `Value` kind: a [`CycleSlot`] is filled after its
/// owner was constructed, so the edge cannot be stated at construction.
///
/// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
pub(crate) fn record_deferred_edge(owner: NodeId, role: EdgeRole, target: Option<NodeId>) {
    let Some(target) = target else {
        return;
    };
    ACTIVE_GRAPH.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(graph) = slot.as_mut() {
            push_edge(
                graph,
                owner,
                role,
                EdgeKind::Value { deferred: true },
                target,
            );
        }
    });
}

/// Append an edge onto an operator already in the graph.
fn push_edge(
    graph: &mut OperatorGraph,
    owner: NodeId,
    role: EdgeRole,
    kind: EdgeKind,
    target: NodeId,
) {
    for node in &mut graph.nodes {
        if let GraphNode::Operator { id, inputs, .. } = node
            && *id == owner
        {
            inputs.push(InputEdge { role, kind, target });
            return;
        }
    }
}

fn resolve(specs: &[InputEdgeSpec]) -> Vec<InputEdge> {
    specs
        .iter()
        .filter_map(|s| {
            s.target.map(|target| InputEdge {
                role: s.role.clone(),
                kind: s.kind,
                target,
            })
        })
        .collect()
}
