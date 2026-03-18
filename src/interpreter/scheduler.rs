use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::interpreter::{Consumer, DataSourceDomainExtentImpl};

/// Basic scheduler implementation.
///
/// Tracks [`IterateExtentHandle`]s that generate data from external sources (e.g.
/// data sources) and need to be polled for new data each tick.
#[derive(Default)]
pub struct Scheduler {
    source_handles: HashMap<String, SourceHandle>,
}

type SourceHandle = (
    Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    Vec<Box<dyn Consumer>>,
);

impl Scheduler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Use when the scheduler will be intentionally unused.
    pub fn noop() -> Self {
        Self::default()
    }

    pub fn add_source_handle(
        &mut self,
        handle: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        consumer: Box<dyn Consumer>,
    ) {
        let id = handle.borrow().get_id().to_string();
        if let Some(entry) = self.source_handles.get_mut(&id) {
            assert!(Rc::ptr_eq(&handle, &entry.0));
            entry.1.push(consumer);
        } else {
            self.source_handles.insert(id, (handle, vec![consumer]));
        }
    }

    pub fn check_for_notifications(&mut self) {
        self.source_handles
            .values_mut()
            .for_each(|(source, consumers)| {
                if source.borrow_mut().check_for_new_data() {
                    consumers.iter_mut().for_each(|c| c.notify());
                }
            });
    }
}
