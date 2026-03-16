use std::{cell::RefCell, rc::Rc};

use crate::interpreter::tile_operators::IterateExtentHandle;
use crate::interpreter::{Producer, VarProducer};
use crate::pretty_graph::VizOptions;
use crate::pretty_tree::InspectNode;

// Basic scheduler implementation.
// For now, this only tracks variables that generate data and need to be
// checked for notifications.
#[derive(Default)]
pub struct Scheduler {
    sources: Vec<Rc<RefCell<VarProducer>>>,
    source_handles: Vec<IterateExtentHandle>,
}

impl Scheduler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Use when the scheduler will be intentionally unused.
    pub fn noop() -> Self {
        Self::default()
    }

    pub fn add_source(&mut self, var_sub: Rc<RefCell<VarProducer>>) {
        self.sources.push(var_sub);
    }

    pub fn add_iterate_handle(&mut self, handle: IterateExtentHandle) {
        self.source_handles.push(handle);
    }

    pub fn check_for_notifications(&mut self) {
        self.sources
            .iter()
            .for_each(|s| s.borrow_mut().check_for_notification());
        self.source_handles
            .iter_mut()
            .for_each(|s| s.check_for_notification());
    }

    /// Inspect all registered sources for the web dashboard.
    pub fn inspect_sources(&self) -> Vec<InspectNode> {
        let opts = VizOptions::default();
        self.sources
            .iter()
            .map(|s| s.borrow().inspect(&opts))
            .collect()
    }
}
