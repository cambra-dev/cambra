//! The source an `env_var("NAME")` call reads: one environment variable's value.

use std::collections::HashSet;
use std::rc::Rc;

use crate::ccl::Type;
use crate::interpreter::{
    BaseType, ColumnValue, DataSourceDomainExtentImpl, Extent, Value,
    producer_releases::ProducerReleases, tiling::Predicate,
};

/// How a host reads an environment variable: its value, or `None` when it is unset or is not
/// UTF-8.
///
/// A function rather than a snapshot of the environment, so the host reads exactly the
/// variables a program names. `main` reads the process environment; a test supplies its own.
#[derive(Clone)]
pub struct EnvLookup(Rc<LookupFn>);

type LookupFn = dyn Fn(&str) -> Option<String>;

impl EnvLookup {
    pub fn new(lookup: impl Fn(&str) -> Option<String> + 'static) -> Self {
        Self(Rc::new(lookup))
    }

    /// The process environment.
    pub fn process() -> Self {
        Self::new(|name| std::env::var(name).ok())
    }

    pub fn get(&self, name: &str) -> Option<String> {
        (self.0)(name)
    }
}

impl Default for EnvLookup {
    fn default() -> Self {
        Self::process()
    }
}

/// The source of one environment variable, named [`env_var_source_name`] of the variable.
///
/// Lowering creates it empty, so compiling reads no environment. The host fills it before the
/// version that reads it starts ([`fill`](Self::fill)), and the value is then the source's one
/// element, at position 0, and the source is finished.
///
/// The value is a constant for the life of the process, so the source never drops it. A
/// release records what one producer has read, so no producer reads the value twice. A producer
/// registering later, such as one a reload adds, reads it from the start: unlike a stream, the
/// source has no history a replacement version already summarizes, only a value every reader
/// needs.
pub struct EnvVarSource {
    source_name: String,
    value: Option<String>,
    has_news: bool,
    releases: ProducerReleases,
}

/// The name of the source that holds environment variable `var`.
///
/// The `__` prefix keeps it out of reach of a user's call, which cannot spell a name with a
/// colon in it.
pub fn env_var_source_name(var: &str) -> String {
    format!("__env:{var}")
}

impl EnvVarSource {
    pub fn new(var: &str) -> Self {
        Self {
            source_name: env_var_source_name(var),
            value: None,
            has_news: false,
            releases: ProducerReleases::default(),
        }
    }

    pub fn is_filled(&self) -> bool {
        self.value.is_some()
    }

    /// Set the variable's value and finish the source.
    pub fn fill(&mut self, value: String) {
        debug_assert!(
            self.value.is_none(),
            "{} is filled once: its value is fixed for the life of the process",
            self.source_name
        );
        self.value = Some(value);
        self.has_news = true;
    }
}

impl DataSourceDomainExtentImpl for EnvVarSource {
    fn get_id(&self) -> &str {
        &self.source_name
    }

    fn check_for_new_data(&mut self) -> bool {
        std::mem::take(&mut self.has_news)
    }

    fn get_yield_predicate(&self) -> Predicate {
        if self.value.is_some() {
            Predicate::True
        } else {
            Predicate::False
        }
    }

    fn get_elements(&self, producer: &str) -> ColumnValue {
        let read = self
            .releases
            .of(producer)
            .is_some_and(|released| released.subsumes(&Predicate::at_or_below(Value::UInt(0))));
        ColumnValue::UInts(if self.value.is_some() && !read {
            vec![0]
        } else {
            Vec::new()
        })
    }

    fn element_extent(&self) -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn get(&self, keys: ColumnValue) -> ColumnValue {
        let ColumnValue::UInts(keys) = keys else {
            panic!(
                "{} is keyed by UInt positions, got {keys:?}",
                self.source_name
            );
        };
        let value = self
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{} is read before it is filled", self.source_name));
        ColumnValue::Strings(
            keys.iter()
                .map(|&k| {
                    assert_eq!(k, 0, "{} holds one element, at 0", self.source_name);
                    value.as_str().into()
                })
                .collect(),
        )
    }

    fn output_value_extent(&self) -> Extent {
        Extent::Base(BaseType::String)
    }

    fn output_type(&self) -> Type {
        Type::Base(BaseType::String)
    }

    fn release(&mut self, producer: &str, obsolete: Predicate) {
        self.releases.record(producer, &obsolete);
    }

    fn carry_release_to_new_producers(&mut self, _predecessor: &HashSet<String>) {
        // A new producer reads the value from the start; see the type's documentation.
    }

    fn first_position_for_a_new_producer(&self) -> u64 {
        0
    }

    fn retire_producer(&mut self, producer: &str) {
        self.releases.retire(producer);
    }
}
