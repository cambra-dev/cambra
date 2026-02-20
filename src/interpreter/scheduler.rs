use std::{cell::RefCell, rc::Rc};

use crate::interpreter::{Producer, VarProducer};
use crate::pretty_graph::VizOptions;
use crate::pretty_tree::InspectNode;

// Basic scheduler implementation.
// For now, this only tracks variables that generate data and need to be
// checked for notifications.
#[derive(Default)]
pub struct Scheduler {
    sources: Vec<Rc<RefCell<VarProducer>>>,
}

impl Scheduler {
    pub fn new() -> Self {
        Scheduler {
            sources: Vec::new(),
        }
    }

    pub fn add_source(&mut self, var_sub: Rc<RefCell<VarProducer>>) {
        self.sources.push(var_sub);
    }

    pub fn check_for_notifications(&self) {
        self.sources
            .iter()
            .for_each(|s| s.borrow_mut().check_for_notification());
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
