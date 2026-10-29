//! The static structure of the dataflow operator graph.
//!
//! [`BoundarySession::into_graph`] walks from program outputs through
//! [`TileOperator::visit_inputs`]. Conversion records sink identities separately.
//!
//! Walk newly constructed operators before subscription: subscribing consumes late-wired
//! inputs. Stored edges point from consumers to inputs; dataflow runs in the reverse direction.
//!
//! Edge ownership, traversal, and source attribution are specified in
//! `src/interpreter/design-operators.md`, "Operator identity and the graph the inspector reads".
//!
//! [`TileOperator::visit_inputs`]: crate::interpreter::tile_operators::TileOperator::visit_inputs

use smol_str::SmolStr;
use std::cell::RefCell;

use crate::ccl::provenance::NodeId;
use crate::interpreter::tile_operators::TileOperator;
use crate::interpreter::tiling::Tiling;

/// How a downstream operator holds one of its inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    /// An exclusively owned `Box<dyn TileOperator>`.
    ///
    /// `deferred` marks an input wired through a [`CycleSlot`] after its owner was constructed.
    /// It does not change exclusive ownership.
    ///
    /// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
    Value { deferred: bool },
    /// A `FanOutSlot`'s edge to its fan input, which other slots may also reach.
    /// Excluded from the exclusive-ownership forest.
    Share,
}

/// What names an input at its consumer.
///
/// Named fields, vector positions, and store keys remain distinct even when their labels match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgeRole {
    /// The field the consumer stores the input under, e.g. `"input"`,
    /// `"predicate"`, `"default"`.
    Named(&'static str),
    /// A position in a `Vec` of inputs, as `Zip` and `UnionOperator` have.
    Positional(usize),
    /// A store key, as a store's keyed inputs are.
    StoreKey(String),
}

/// Display label used by operator inspection and the wire's `OperatorEdgeRole`.
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

/// One input edge, as the operator holding it states it.
pub struct InputEdgeSpec<'a> {
    pub(crate) role: EdgeRole,
    pub(crate) kind: EdgeKind,
    pub(crate) target: &'a dyn TileOperator,
}

/// An owned input held under a named field.
pub(crate) fn value<'a>(role: &'static str, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Named(role),
        kind: EdgeKind::Value { deferred: false },
        target: op,
    }
}

/// An owned input at a position in a `Vec`.
pub(crate) fn value_at<'a>(index: usize, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Positional(index),
        kind: EdgeKind::Value { deferred: false },
        target: op,
    }
}

/// An owned input keyed by a store key, as a store's per-key seeds are.
pub(crate) fn value_keyed<'a>(
    key: impl Into<String>,
    op: &'a dyn TileOperator,
) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::StoreKey(key.into()),
        kind: EdgeKind::Value { deferred: false },
        target: op,
    }
}

/// An owned input wired through a [`CycleSlot`] after its holder was built.
///
/// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
pub(crate) fn value_late<'a>(role: EdgeRole, op: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role,
        kind: EdgeKind::Value { deferred: true },
        target: op,
    }
}

/// A slot's shared edge to its fan input, whether or not the edge belongs to a cycle.
pub(crate) fn share<'a>(fan_input: &'a dyn TileOperator) -> InputEdgeSpec<'a> {
    InputEdgeSpec {
        role: EdgeRole::Named("fan"),
        kind: EdgeKind::Share,
        target: fan_input,
    }
}

/// An operator or compiled output boundary. An output field has a sink node but no operator.
#[derive(Clone, Debug)]
pub enum GraphNode {
    /// An operator, with the inputs it holds.
    Operator {
        id: NodeId,
        kind: &'static str,
        tiling: Tiling,
        inputs: Vec<InputEdge>,
    },
    /// A compiled output field. Out-degree 0, and a start of every walk.
    Sink {
        id: NodeId,
        name: String,
        input: InputEdge,
    },
}

/// The static operator graph of one compiled program.
///
/// Nodes are emitted in depth-first postorder, visiting outputs and inputs in their supplied
/// order. A visited set prevents repeated emission and recursion through cycles. Each output's
/// sink follows the traversal of its input.
#[derive(Clone, Debug, Default)]
pub struct OperatorGraph {
    nodes: Vec<GraphNode>,
}

impl OperatorGraph {
    /// Every node, in walk order.
    pub fn nodes(&self) -> &[GraphNode] {
        &self.nodes
    }

    /// Nodes that no `Value` edge targets, in node order: roots of the ownership forest.
    /// Sinks and shared fan inputs qualify. [`assert_graph_invariants`] checks that these
    /// roots reach every recorded node through `Value` edges alone.
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
            GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => *id,
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
                }
            })
    }
}

/// In debug and test builds, check edge targets, exclusive ownership, and reachability from
/// [`OperatorGraph::walk_starts`] through `Value` edges. Together these require a value-edge
/// forest.
/// A value-edge cycle has no root and cannot be entered by another value edge without violating
/// exclusive ownership. The check covers recorded nodes, not operators omitted from the graph.
///
/// The item exists in every build so release callers compile; the body returns immediately when
/// neither `debug_assertions` nor `test` is enabled.
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
    // and every node nothing owns — a sink, a fan input — is in
    // `walk_starts` already, so no share edge has to be followed to reach one.
    let mut seen: std::collections::HashSet<NodeId> = std::collections::HashSet::new();
    let mut stack: Vec<NodeId> = graph.walk_starts();
    let by_id: std::collections::HashMap<NodeId, &GraphNode> = graph
        .nodes()
        .iter()
        .map(|n| match n {
            GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => (*id, n),
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
            None => {}
        }
    }
    let stranded: Vec<String> = ids
        .difference(&seen)
        .map(|id| match by_id.get(id) {
            Some(GraphNode::Operator { kind, tiling, .. }) => format!("{id:?} {kind} {tiling}"),
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

/// Per-compilation sink identities and the set of reused operators already attributed.
/// Sink edges and operator nodes are obtained by walking the outputs.
#[derive(Default)]
struct Boundaries {
    /// Each compiled output field's node.
    sinks: Vec<(SmolStr, NodeId)>,
    /// Operators this compile took from the version it replaces, already rowed
    /// by [`record_kept_operators`]. One fan-out reaches several bindings, and a
    /// second row for one id is a defect the table asserts on.
    rowed_kept: std::collections::HashSet<NodeId>,
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
    /// Call before subscribing newly constructed operators: subscription consumes
    /// [`CycleSlot`] contents and store inputs. Already-subscribed reused operators expose
    /// only the inputs they still hold.
    ///
    /// [`CycleSlot`]: crate::interpreter::tile_operators::CycleSlot
    pub(crate) fn into_graph(self, outputs: &[(SmolStr, Box<dyn TileOperator>)]) -> OperatorGraph {
        let boundaries = BOUNDARIES
            .with(|slot| slot.borrow_mut().take())
            .unwrap_or_default();
        let mut nodes = Vec::new();
        let mut seen = std::collections::HashSet::new();

        for (name, op) in outputs {
            walk_operator(&**op, &mut seen, &mut nodes);
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
                name: name.to_string(),
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

/// Emit reachable operators in depth-first postorder, skipping previously visited ids.
///
/// An operator with no id is neither emitted nor traversed. Test doubles can omit identities.
fn walk_operator(
    op: &dyn TileOperator,
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
        walk_operator(spec.target, seen, nodes);
        let Some(subscribed) = spec.target.operator_id() else {
            return;
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

/// Row every operator in `op`'s subgraph against the expression node whose
/// recording is open.
///
/// A version replacing another keeps operators the previous compile built, ids
/// and all ([`OpConversionContext::keep_region`]), and this compile never walks
/// into one — so nothing mints them and they reach the `post-conversion` pane
/// with no row. Rowing them here gives a kept operator the same attribution a
/// rebuilt one gets: the binding it now sits at, in the program the user is
/// running.
///
/// The descent is [`TileOperator::visit_inputs`], the same one
/// [`BoundarySession::into_graph`] makes, so what is rowed is exactly what the
/// pane will hold. A kept store has already been subscribed, so its body is out
/// of reach of both walks alike.
///
/// [`OpConversionContext::keep_region`]: crate::interpreter::operator_conversion::OpConversionContext
pub(crate) fn record_kept_operators(op: &dyn TileOperator) {
    let Some(id) = op.operator_id() else {
        return;
    };
    let fresh = BOUNDARIES.with(|slot| match slot.borrow_mut().as_mut() {
        Some(boundaries) => boundaries.rowed_kept.insert(id),
        None => false,
    });
    if !fresh {
        return;
    }
    crate::ccl::provenance::on_mint(id);
    op.visit_inputs(&mut |spec| {
        record_kept_operators(spec.target);
    });
}

/// Each data source's `IterateExtent`s, by the name the source was registered
/// under.
///
/// A source is not a node, so what attaches to a source attaches to the
/// iterations over its domain: the operators the scheduler wakes when it
/// produces. Read off each iteration's tiling, whose domain is the extent it
/// iterates. A source the program iterates nowhere has no entry.
///
/// Derived from the current graph, including any operators reused from an earlier version.
pub fn source_nodes(graph: &OperatorGraph) -> std::collections::HashMap<String, Vec<NodeId>> {
    use crate::interpreter::tile_operators::{IterateExtent, short_type_name};

    let mut out: std::collections::HashMap<String, Vec<NodeId>> = std::collections::HashMap::new();
    for node in graph.nodes() {
        let GraphNode::Operator {
            id, kind, tiling, ..
        } = node
        else {
            continue;
        };
        if *kind != short_type_name::<IterateExtent>() {
            continue;
        }
        let Tiling::DataFunction { domain, .. } = tiling else {
            debug_assert!(
                false,
                "operator graph: IterateExtent {id:?} has tiling {tiling}, but an iteration's \
                 tiling is a collection over the extent it iterates"
            );
            continue;
        };
        domain.for_each_source(&mut |source| {
            let ids = out.entry(source.borrow().get_id().to_string()).or_default();
            if !ids.contains(id) {
                ids.push(*id);
            }
        });
    }
    out
}

/// Mint the node for a compiled output field.
pub(crate) fn record_sink(name: &str) {
    let id = NodeId::fresh();
    crate::ccl::provenance::on_mint(id);
    BOUNDARIES.with(|slot| {
        if let Some(boundaries) = slot.borrow_mut().as_mut() {
            boundaries.sinks.push((SmolStr::new(name), id));
        }
    });
}
