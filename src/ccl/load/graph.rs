//! The module graph's cycles and link order (`docs/modules.md`, "Linking").
//!
//! Both are functions of the graph and the modules' paths alone. Neither
//! depends on the order files were found in, which numbers the [`FileId`]s, or
//! on the order of statements in a file.

use super::{CycleStep, LoadError, LoadedModule, module_name};
use crate::chl_parser::{FileId, ModulePath, SourceMap};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// The key modules are ordered by: the module path, and a root no module path
/// names before every module.
fn key(sources: &SourceMap, file: FileId) -> Option<&ModulePath> {
    sources.module(file)
}

/// One error per strongly connected component of the module graph that has a
/// cycle, naming one cycle in it.
///
/// The cycle reported is the shortest through the component's least module,
/// following edges in statement order, and components are reported in the
/// order of their least modules.
pub(super) fn cycles(modules: &[LoadedModule], sources: &SourceMap) -> Vec<LoadError> {
    let index: BTreeMap<FileId, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.file, i))
        .collect();
    let successors: Vec<Vec<usize>> = modules
        .iter()
        .map(|m| m.edges.iter().map(|e| index[&e.target]).collect())
        .collect();

    let mut components: Vec<Vec<usize>> = strongly_connected(&successors)
        .into_iter()
        .filter(|c| c.len() > 1 || successors[c[0]].contains(&c[0]))
        .collect();
    for component in &mut components {
        component.sort_by_key(|&i| key(sources, modules[i].file));
    }
    components.sort_by_key(|c| key(sources, modules[c[0]].file));

    components
        .iter()
        .map(|component| {
            let start = component[0];
            let inside: BTreeSet<usize> = component.iter().copied().collect();
            // Breadth-first from `start` within the component: `via[n]` is the
            // module and edge `n` was first reached by.
            let mut via: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
            let mut queue = VecDeque::from([start]);
            let mut closing = None;
            'search: while let Some(at) = queue.pop_front() {
                for (e, edge) in modules[at].edges.iter().enumerate() {
                    let to = index[&edge.target];
                    if to == start {
                        closing = Some((at, e));
                        break 'search;
                    }
                    if inside.contains(&to) && !via.contains_key(&to) {
                        via.insert(to, (at, e));
                        queue.push_back(to);
                    }
                }
            }
            let (mut at, e) = closing.expect("a cyclic component has a cycle through each module");
            let mut path = vec![(at, e)];
            while at != start {
                let (from, e) = via[&at];
                path.push((from, e));
                at = from;
            }
            path.reverse();
            let steps = path
                .into_iter()
                .map(|(from, e)| {
                    let edge = &modules[from].edges[e];
                    CycleStep {
                        span: edge.span,
                        kind: edge.kind,
                        from: module_name(sources, modules[from].file),
                        to: module_name(sources, edge.target),
                    }
                })
                .collect();
            LoadError::Cycle { steps }
        })
        .collect()
}

/// Every module, each after every module it has an edge to, ties broken by
/// module path. The graph must be acyclic.
pub(super) fn link_order(modules: &[LoadedModule], sources: &SourceMap) -> Vec<FileId> {
    let mut waiting: BTreeMap<FileId, BTreeSet<FileId>> = modules
        .iter()
        .map(|m| (m.file, m.edges.iter().map(|e| e.target).collect()))
        .collect();
    let mut dependents: BTreeMap<FileId, Vec<FileId>> = BTreeMap::new();
    for (&file, targets) in &waiting {
        for &target in targets {
            dependents.entry(target).or_default().push(file);
        }
    }
    let mut ready: BTreeSet<(Option<&ModulePath>, FileId)> = waiting
        .iter()
        .filter(|(_, targets)| targets.is_empty())
        .map(|(&file, _)| (key(sources, file), file))
        .collect();

    let mut order = Vec::with_capacity(modules.len());
    while let Some((_, file)) = ready.pop_first() {
        order.push(file);
        for &dependent in dependents.get(&file).into_iter().flatten() {
            let targets = waiting.get_mut(&dependent).expect("every module waits");
            targets.remove(&file);
            if targets.is_empty() {
                ready.insert((key(sources, dependent), dependent));
            }
        }
    }
    assert_eq!(
        order.len(),
        modules.len(),
        "an acyclic module graph orders every module"
    );
    order
}

/// The strongly connected components of the graph `successors`, by Tarjan's
/// algorithm.
fn strongly_connected(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct Tarjan<'a> {
        successors: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        components: Vec<Vec<usize>>,
    }

    impl Tarjan<'_> {
        fn visit(&mut self, v: usize) {
            self.index[v] = Some(self.next);
            self.low[v] = self.next;
            self.next += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for &w in &self.successors[v] {
                match self.index[w] {
                    None => {
                        self.visit(w);
                        self.low[v] = self.low[v].min(self.low[w]);
                    }
                    Some(w_index) if self.on_stack[w] => {
                        self.low[v] = self.low[v].min(w_index);
                    }
                    Some(_) => {}
                }
            }
            if Some(self.low[v]) == self.index[v] {
                let mut component = Vec::new();
                loop {
                    let w = self.stack.pop().expect("v is on the stack");
                    self.on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                self.components.push(component);
            }
        }
    }

    let n = successors.len();
    let mut tarjan = Tarjan {
        successors,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
        components: Vec::new(),
    };
    for v in 0..n {
        if tarjan.index[v].is_none() {
            tarjan.visit(v);
        }
    }
    tarjan.components
}
