use std::{cell::RefCell, rc::Rc};

use crate::interpreter::{InspectNode, Producer, VarSub};

// Basic scheduler implementation.
// For now, this only tracks variables that generate data and need to be
// checked for notifications.
#[derive(Default)]
pub struct Scheduler {
    sources: Vec<Rc<RefCell<VarSub>>>,
}

impl Scheduler {
    pub fn new() -> Self {
        Scheduler {
            sources: Vec::new(),
        }
    }

    pub fn add_source(&mut self, var_sub: Rc<RefCell<VarSub>>) {
        self.sources.push(var_sub);
    }

    pub fn check_for_notifications(&self) {
        self.sources
            .iter()
            .for_each(|s| s.borrow_mut().check_for_notification());
    }

    /// Inspect all registered sources for the web dashboard.
    pub fn inspect_sources(&self) -> Vec<InspectNode> {
        self.sources.iter().map(|s| s.borrow().inspect()).collect()
    }
}
