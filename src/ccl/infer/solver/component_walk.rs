//! The bookkeeping of a memoized walk over a graph that may cycle, which finishes each strongly
//! connected component it discovers before any result inside the component is final.
//!
//! The solver's walks over the bound graph ([`super::compact`]'s `compact_go` and
//! [`super::spec_key`]'s `key_go`) each compute one value per key, and a key's value is computed
//! from the values of the keys its bounds reach. The graph cycles:
//! inference records `?a <: ?b` and `?b <: ?a` alike, and a data domain is drawn in both
//! directions. A key reached again while it is being expanded is a **back edge**.
//!
//! A value computed from back edges depends on the path that reached it unless the walk knows
//! what each back edge stands for. This walk keeps, for each key, its value from the previous
//! round of its component, and a back edge reads that value. So a key's value depends only on
//! the key and the previous round, which a whole round shares. The walk memoizes a value inside
//! a component that is still open (**pending**), and a reuse joins the reusing key to that
//! component.
//!
//! A key whose expansion reached no key entered before it is the **root** of a component
//! (Tarjan's algorithm, run online: the graph is discovered by the walk). The component is
//! every key finished since the root was entered that is still pending. A component with no
//! cycle is final at once. A cyclic one is walked again from its root until a round leaves
//! every member's value unchanged; the first round reads nothing at a back edge. The members'
//! values are then final.
//!
//! The values must form a fixpoint that a round reaches, which holds where a key's value
//! merges what its bounds contribute by an operation where merging a value again changes
//! nothing. A component still changing after the walk's bound on rounds is unsettled
//! ([`Exit::Unsettled`]), and the caller decides what that means.
//!
//! A back edge reads its target's value from the last round, so a contribution travels one
//! back edge per round, and a component that is a long chain takes as many rounds as it is
//! long. A **uniform** key is one whose value is the merge of its bounds' values, each carried
//! unchanged ([`ComponentWalk::exit`]'s caller says which keys are). In a component of uniform
//! keys every member reaches every contribution the root's first round merged and adds
//! nothing. The second round starts every back edge from the root's value, so each member's
//! value holds all of it, and the second round's values are final. They are each member's
//! own merge rather than a copy of the root's: a merge that records which contribution it met
//! first records the member's own first.
//!
//! A back edge through a structural intermediary is a recursive type rather than a cycle of
//! one value, and the walk does not iterate over it: the caller answers it with a placeholder
//! or truncates it, and [`ComponentWalk::recursive_edge`] keeps every key above its target from
//! being memoized ([`ComponentWalk::taint_from`] in general).

use std::collections::HashMap;
use std::hash::Hash;

/// Where a key entered at some index stands.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Status {
    /// Being expanded.
    Expanding,
    /// Finished, in a component that is still open.
    Pending,
    /// Finished in a finished component.
    Final,
    /// Finished in a round its component has since discarded.
    Stale,
}

/// A key being expanded.
struct Frame<K> {
    key: K,
    index: usize,
    /// The lowest index of a key in an open component that this expansion reached.
    low: usize,
    /// The lowest index of a key a recursive edge or a truncation below this expansion keeps
    /// from being memoized: this key's value is memoizable if its index is lower.
    tainted_from: usize,
    /// Whether a back edge returned to this key itself.
    self_edge: bool,
}

/// How a key's expansion finished ([`ComponentWalk::exit`]).
pub(super) enum Exit {
    /// The value is final, or pending in an open component; memoize it under `index` unless
    /// `memoizable` is false: a recursive edge or a truncation below it reached above it.
    Done { index: usize, memoizable: bool },
    /// The key is the root of a cyclic component whose round changed a value: expand it again.
    Rerun,
    /// The key is the root of a cyclic component still changing after the walk's bound on
    /// rounds. Its members' values are discarded.
    Unsettled,
}

/// The state of one walk ([`self`](self)).
pub(super) struct ComponentWalk<K, V> {
    status: Vec<Status>,
    frames: Vec<Frame<K>>,
    expanding: HashMap<K, usize>,
    /// Finished keys in open components, in entry order, each with whether it is uniform:
    /// Tarjan's stack.
    open: Vec<(usize, K, bool)>,
    /// Each open member's value in its component's last finished round, which a back edge
    /// reads.
    previous: HashMap<K, V>,
    /// Each open member's value in its component's current round.
    current: HashMap<K, V>,
    /// How many rounds each root of a cyclic component has been walked again.
    rounds: HashMap<K, usize>,
    /// The roots of uniform components whose members' values were set to the root's.
    seeded: std::collections::HashSet<K>,
    /// The bound on [`rounds`](Self::rounds).
    max_rounds: usize,
}

impl<K: Clone + Eq + Hash, V: Clone + PartialEq> ComponentWalk<K, V> {
    /// A walk that walks a cyclic component at most `max_rounds` times.
    pub(super) fn new(max_rounds: usize) -> Self {
        ComponentWalk {
            status: Vec::new(),
            frames: Vec::new(),
            expanding: HashMap::new(),
            open: Vec::new(),
            previous: HashMap::new(),
            current: HashMap::new(),
            rounds: HashMap::new(),
            seeded: std::collections::HashSet::new(),
            max_rounds,
        }
    }

    /// Whether `key` is being expanded.
    pub(super) fn expanding(&self, key: &K) -> bool {
        self.expanding.contains_key(key)
    }

    /// Start expanding `key`, which is not being expanded.
    pub(super) fn enter(&mut self, key: K) {
        let index = self.status.len();
        self.status.push(Status::Expanding);
        let previous = self.expanding.insert(key.clone(), index);
        debug_assert!(
            previous.is_none(),
            "a key entered while it is being expanded"
        );
        self.frames.push(Frame {
            key,
            index,
            low: index,
            tainted_from: usize::MAX,
            self_edge: false,
        });
    }

    /// The value a back edge to `key`, which is being expanded, reads: `key`'s value in its
    /// component's last round, `None` in the first.
    pub(super) fn back_edge(&mut self, key: &K) -> Option<V> {
        let index = self.expanding[key];
        let top = self
            .frames
            .last_mut()
            .expect("a back edge is read inside an expansion");
        top.low = top.low.min(index);
        if index == top.index {
            top.self_edge = true;
        }
        self.previous.get(key).cloned()
    }

    /// Record an edge to `key`, which is being expanded, that the caller answers as a
    /// recursive type: no key entered after `key` and above this edge is memoized.
    pub(super) fn recursive_edge(&mut self, key: &K) {
        let index = self.expanding[key];
        self.taint_from(index + 1);
    }

    /// The index of the innermost key being expanded.
    pub(super) fn innermost(&self) -> Option<usize> {
        self.frames.last().map(|f| f.index)
    }

    /// The index the next key entered takes: every key entered from here on has this index or
    /// a higher one.
    pub(super) fn next_index(&self) -> usize {
        self.status.len()
    }

    /// The index `key`, which is being expanded, was entered at.
    pub(super) fn entered_at(&self, key: &K) -> usize {
        self.expanding[key]
    }

    /// Keep every key being expanded whose index is `index` or higher from being memoized.
    pub(super) fn taint_from(&mut self, index: usize) {
        if let Some(top) = self.frames.last_mut() {
            top.tainted_from = top.tainted_from.min(index);
        }
    }

    /// Whether a value memoized under `index` may be reused here. A value in an open component
    /// joins the current key to that component.
    pub(super) fn reuse(&mut self, index: usize) -> bool {
        match self.status[index] {
            Status::Final => true,
            Status::Pending => {
                let top = self
                    .frames
                    .last_mut()
                    .expect("a reuse is read inside an expansion");
                top.low = top.low.min(index);
                true
            }
            Status::Stale => false,
            Status::Expanding => unreachable!("a value is memoized only once its key finishes"),
        }
    }

    /// Finish expanding the innermost key, whose value is `value`. `uniform` says the value is
    /// the merge of its bounds' values, each carried unchanged ([`self`](self)).
    pub(super) fn exit(&mut self, value: &V, uniform: bool) -> Exit {
        let frame = self.frames.pop().expect("an exit matches an enter");
        self.expanding.remove(&frame.key);
        if let Some(parent) = self.frames.last_mut() {
            parent.low = parent.low.min(frame.low);
            parent.tainted_from = parent.tainted_from.min(frame.tainted_from);
        }
        let index = frame.index;
        let memoizable = index < frame.tainted_from;
        if frame.low < index {
            self.status[index] = Status::Pending;
            self.current.insert(frame.key.clone(), value.clone());
            self.open.push((index, frame.key, uniform));
            return Exit::Done { index, memoizable };
        }
        let first = self.open.partition_point(|(i, _, _)| *i < index);
        if first == self.open.len() && !frame.self_edge {
            self.status[index] = Status::Final;
            return Exit::Done { index, memoizable };
        }
        let members: Vec<(usize, K, bool)> = self.open.drain(first..).collect();
        self.current.insert(frame.key.clone(), value.clone());
        let keys = || {
            members
                .iter()
                .map(|(_, k, _)| k)
                .chain(std::iter::once(&frame.key))
        };
        let settled = keys().all(|k| self.previous.get(k) == self.current.get(k));
        let settled = self.seeded.remove(&frame.key) || settled;
        let rounds = self.rounds.entry(frame.key.clone()).or_default();
        let seed = *rounds == 0 && uniform && members.iter().all(|(_, _, u)| *u);
        *rounds += 1;
        let unsettled = !settled && *rounds >= self.max_rounds;
        let settles = if settled {
            Status::Final
        } else {
            Status::Stale
        };
        for (i, _, _) in &members {
            self.status[*i] = settles;
        }
        self.status[index] = if unsettled { Status::Final } else { settles };
        for k in keys() {
            let mine = self.current.remove(k);
            if settled || unsettled {
                self.previous.remove(k);
            } else if seed {
                self.previous.insert(k.clone(), value.clone());
            } else if let Some(mine) = mine {
                self.previous.insert(k.clone(), mine);
            }
        }
        if seed && !settled {
            self.seeded.insert(frame.key.clone());
        }
        if settled || unsettled {
            self.rounds.remove(&frame.key);
        }
        if settled {
            Exit::Done { index, memoizable }
        } else if unsettled {
            Exit::Unsettled
        } else {
            Exit::Rerun
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    /// A graph whose nodes each hold labels, every edge carrying a node's labels to its
    /// predecessor through a map of labels, `None` for the identity; a node's value is its
    /// labels and every successor's value carried back through the edge.
    struct Graph {
        labels: Vec<BTreeSet<u32>>,
        edges: Vec<Vec<Edge>>,
    }

    /// The node an edge reaches and the map it carries labels through.
    type Edge = (usize, Option<fn(u32) -> u32>);

    struct Walk<'g> {
        graph: &'g Graph,
        walk: ComponentWalk<usize, BTreeSet<u32>>,
        memo: HashMap<usize, (BTreeSet<u32>, usize)>,
        expansions: usize,
    }

    impl Walk<'_> {
        fn value(&mut self, node: usize) -> BTreeSet<u32> {
            if self.walk.expanding(&node) {
                return self.walk.back_edge(&node).unwrap_or_default();
            }
            if let Some((value, index)) = self.memo.get(&node)
                && self.walk.reuse(*index)
            {
                return value.clone();
            }
            let graph = self.graph;
            // Every edge out of the node carries labels unchanged.
            let uniform = graph.edges[node].iter().all(|(_, f)| f.is_none());
            loop {
                self.walk.enter(node);
                self.expansions += 1;
                let mut value = graph.labels[node].clone();
                for (to, f) in &graph.edges[node] {
                    let below = self.value(*to);
                    value.extend(below.into_iter().map(|l| f.map_or(l, |f| f(l))));
                }
                match self.walk.exit(&value, uniform) {
                    Exit::Done { index, .. } => {
                        self.memo.insert(node, (value.clone(), index));
                        return value;
                    }
                    Exit::Rerun => {}
                    Exit::Unsettled => panic!("the toy graph's values settle"),
                }
            }
        }
    }

    fn walk(graph: &Graph) -> Walk<'_> {
        Walk {
            graph,
            walk: ComponentWalk::new(64),
            memo: HashMap::new(),
            expansions: 0,
        }
    }

    /// Two nodes per level, each reaching both nodes of the level below and of the level
    /// above: one component, reached along `2ⁿ` paths. Every node's value is every label, and
    /// each node is expanded in the first round and the second, and no more.
    #[test]
    fn a_uniform_component_settles_in_two_rounds_whatever_its_paths() {
        let levels = 24;
        let nodes = 2 * levels;
        let mut edges = vec![Vec::new(); nodes];
        for level in 0..levels - 1 {
            for from in [2 * level, 2 * level + 1] {
                for to in [2 * level + 2, 2 * level + 3] {
                    edges[from].push((to, None));
                    edges[to].push((from, None));
                }
            }
        }
        let labels = (0..nodes as u32).map(|n| BTreeSet::from([n])).collect();
        let graph = Graph { labels, edges };
        let mut w = walk(&graph);
        let every: BTreeSet<u32> = (0..nodes as u32).collect();
        assert_eq!(w.value(0), every);
        assert_eq!(w.expansions, 2 * nodes, "two rounds of {nodes} nodes");
        for node in 0..nodes {
            assert_eq!(w.value(node), every, "node {node}, reached after the walk");
        }
        assert_eq!(
            w.expansions,
            2 * nodes,
            "every later read is the memoized value"
        );
    }

    /// Round a cycle whose edge renames, a label comes back as its image, which the node then
    /// holds too, until a round adds nothing.
    #[test]
    fn a_renaming_cycle_iterates_until_nothing_new_arrives() {
        fn next(label: u32) -> u32 {
            (label + 1) % 5
        }
        let graph = Graph {
            labels: vec![BTreeSet::from([0]), BTreeSet::new()],
            edges: vec![vec![(1, None)], vec![(0, Some(next as fn(u32) -> u32))]],
        };
        let mut w = walk(&graph);
        assert_eq!(w.value(0), (0..5).collect());
        assert_eq!(w.value(1), (1..5).chain(0..1).collect());
    }
}
