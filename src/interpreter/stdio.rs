use std::{cell::RefCell, rc::Rc};

use log::debug;

use crate::interpreter::{
    guard_summary, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, FuncBinding,
    GetResult, Guard, InspectNode, Operator, ParentIndices, Producer, Scheduler, Value, VarScope,
};

/// Operator that reads lines from stdin and produces them as output.
/// Indices are produced via StdinDataSource, which also contains a mapping from
/// index to line at that index.
pub struct StdinReader {
    extent: Extent,
    data_source: Rc<RefCell<StdinDataSource>>,
}

impl StdinReader {
    pub fn new() -> StdinReader {
        let data_source = Rc::new(RefCell::new(StdinDataSource::new()));
        StdinReader {
            extent: Extent::Function {
                domain: Box::new(Extent::DataSourceDomain(data_source.clone())),
                codomain: Box::new(Extent::Base(super::BaseType::String)),
            },
            data_source,
        }
    }
}

impl Default for StdinReader {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for StdinReader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StdinReader").finish()
    }
}

impl Operator for StdinReader {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        _intent_guard: Guard,
        _consumer: Box<dyn Consumer>,
        _var_scope: Option<Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        panic!("Cannot subscribe to stdin directly");
    }

    fn subscribe_to_application(
        &mut self,
        intent_guard: Guard,
        _consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        Box::new(StdinProducer::new(
            intent_guard.clone(),
            binding.subscribe(intent_guard, Box::new(|_| {}), var_scope, scheduler),
            self.data_source.clone(),
        ))
    }
}

/// Buffers and tracks lines available on stdin
struct StdinDataSource {
    /// Currently available data
    buffer: Vec<String>,

    /// Offset of indices in the buffer.  Indices less than this have been released
    start_idx: usize,

    /// Logical size of the buffer, including released lines
    ready_size: usize,

    /// Whether EOF has been observed on stdin
    eof_reached: bool,

    /// Whether the source has been released with Universal
    closed: bool,
}

impl StdinDataSource {
    fn new() -> Self {
        Self {
            buffer: Vec::new(),
            start_idx: 0,
            ready_size: 0,
            eof_reached: false,
            closed: false,
        }
    }

    fn get_opt(&self, i: usize) -> Option<&str> {
        if self.closed || self.start_idx > i || i >= self.ready_size {
            None
        } else {
            Some(&self.buffer[i - self.start_idx])
        }
    }

    /// Returns the line at the given index
    fn get(&self, i: usize) -> &str {
        self.get_opt(i)
            .unwrap_or_else(|| panic!("Invalid StdinDataSource::get({})", i))
    }

    fn add(&mut self, line: String) {
        self.buffer.push(line);
        self.ready_size += 1;
    }

    /// Releases all lines up to and including the given index
    fn release_index(&mut self, i: usize) {
        if i >= self.ready_size || i < self.start_idx {
            panic!(
                "Invalid StdinDataSource::release, {} vs {}, {}",
                i, self.ready_size, self.start_idx
            );
        }
        self.buffer.drain(0..(i - self.start_idx + 1));
        self.start_idx = i + 1;
    }

    fn close(&mut self) {
        self.closed = true;
    }
}

impl DataSourceDomainExtentImpl for StdinDataSource {
    fn get_id(&self) -> String {
        "stdin".to_string()
    }

    /// Reads stdin for a newline, blocking until a new line is available or EOF is observed
    fn check_for_new_data(&mut self) -> bool {
        let input = std::io::stdin();
        let mut line = String::new();
        match input.read_line(&mut line) {
            Ok(0) => {
                debug!("EOF reached on stdin");
                // EOF reached
                self.eof_reached = true;
                false
            }
            Ok(_) => {
                if line.ends_with('\n') {
                    line.pop();
                    if line.ends_with('\r') {
                        line.pop();
                    }
                }
                self.add(line);
                // For now, always break. Ideally, we would check if there's any new data immediately
                // available, but that's annoying to do with the standard rust libs
                true
            }
            Err(err) => {
                panic!("Error reading from stdin: {}", err);
            }
        }
    }

    fn get_yield_guard(&self) -> Guard {
        let yield_guard = if self.eof_reached {
            Guard::Universal
        } else if self.start_idx == 0 {
            Guard::Empty
        } else {
            Guard::LessThanOrEq(Value::UInt(self.start_idx - 1))
        };
        debug!("StdinDataSource yielding {:?}", yield_guard);
        yield_guard
    }

    /// Returns the currently readable set of indices
    fn get_elements(&self) -> Box<dyn Iterator<Item = Value>> {
        Box::new((self.start_idx..self.ready_size).map(Value::UInt))
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        debug!("StdinDataSource::release: {:?}", obsolete_guard);
        match &obsolete_guard {
            Guard::LessThanOrEq(Value::UInt(i)) => self.release_index(*i),
            g if g.is_universal() => self.close(),
            _ => {}
        };
        obsolete_guard
    }
}

struct StdinProducer {
    intent_guard: Guard,
    index_producer: Box<dyn Producer>,
    data_source: Rc<RefCell<StdinDataSource>>,
}

impl StdinProducer {
    fn new(
        intent_guard: Guard,
        index_producer: Box<dyn Producer>,
        data_source: Rc<RefCell<StdinDataSource>>,
    ) -> Self {
        Self {
            intent_guard,
            index_producer,
            data_source,
        }
    }
}

impl std::fmt::Debug for StdinProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StdinProducer")
            .field("intent_guard", &self.intent_guard)
            .finish()
    }
}

impl Producer for StdinProducer {
    fn get(&mut self) -> GetResult {
        let GetResult {
            column_value: indices,
            yield_guard,
        } = self.index_producer.get();
        GetResult {
            column_value: ColumnValue {
                values: vec![Value::Function(
                    indices
                        .values
                        .iter()
                        .map(|v| match v {
                            Value::UInt(i) => FuncBinding {
                                input: v.clone(),
                                output: Value::String(
                                    self.data_source.borrow().get(*i).to_string(),
                                ),
                            },
                            _ => panic!("Non-integer as stdin index"),
                        })
                        .collect(),
                )],
                parent_indices: ParentIndices::TopLevelVector,
            },
            // We don't know anything about the contents of stdin, so the yield guard
            // is Universal if the source is closed and Empty otherwise
            yield_guard: yield_guard.to_universal_or_empty(),
        }
    }

    fn release(&mut self, guard: Guard) -> Guard {
        // Currently, we only release in sources based on the indices not the values, so
        // nothing to do here.
        guard
    }

    fn inspect(&self) -> InspectNode {
        InspectNode {
            type_name: "StdinProducer".to_string(),
            label: self.data_source.borrow().get_id(),
            yield_guard: guard_summary(
                &self
                    .data_source
                    .borrow()
                    .get_yield_guard()
                    .to_universal_or_empty(),
            ),
            data_summary: format!("{:?}", self.data_source.borrow().buffer),
            children: vec![self.index_producer.inspect()],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::{stdio::StdinDataSource, DataSourceDomainExtentImpl, Guard};
    use test_log::test;

    #[test]
    fn test_stdin_datasource() {
        let mut source = StdinDataSource::new();
        assert_eq!(Guard::Empty, source.get_yield_guard());
        source.add("a".to_string());
        source.add("b".to_string());
        assert_eq!("a", source.get(0));
        assert_eq!("b", source.get(1));
        assert_eq!(None, source.get_opt(2));
        assert_eq!(Guard::Empty, source.get_yield_guard());
        source.release_index(0);
        assert_eq!(
            Guard::LessThanOrEq(crate::interpreter::Value::UInt(0)),
            source.get_yield_guard()
        );
        assert_eq!(None, source.get_opt(0));
        assert_eq!("b", source.get(1));
        source.add("c".to_string());
        assert_eq!(None, source.get_opt(0));
        assert_eq!("b", source.get(1));
        assert_eq!("c", source.get(2));
        assert_eq!(
            Guard::LessThanOrEq(crate::interpreter::Value::UInt(0)),
            source.get_yield_guard()
        );
        source.release_index(1);
        assert_eq!(
            Guard::LessThanOrEq(crate::interpreter::Value::UInt(1)),
            source.get_yield_guard()
        );
        assert_eq!(None, source.get_opt(0));
        assert_eq!(None, source.get_opt(1));
        assert_eq!("c", source.get(2));
        assert_eq!(
            Guard::LessThanOrEq(crate::interpreter::Value::UInt(1)),
            source.get_yield_guard()
        );
        source.eof_reached = true;
        source.close();
        assert_eq!(None, source.get_opt(0));
        assert_eq!(None, source.get_opt(1));
        assert_eq!(None, source.get_opt(2));
        assert_eq!(Guard::Universal, source.get_yield_guard());
    }
}
