// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::{cell::RefCell, rc::Rc};

use crate::{
    ccl::{infer::TypeInferenceContext, lower::LoweringContext, Type},
    interpreter::{BaseType, DataSourceDomainExtentImpl, TestDataSource},
};

/// Bundles the per-stage registries needed to thread externally-managed data
/// sources through the full CCL pipeline (lowering → type inference → compilation).
///
/// Call [`register_test_source`](Self::register_test_source) or
/// [`register_stdin_source`](Self::register_stdin_source) once per source, then pass
/// each field to the corresponding pipeline stage.
pub struct GlobalContext {
    /// Lowering-stage registry: records which names are source calls.
    lowering: LoweringContext,
    /// Inference-stage registry: supplies the CCL function type for each source.
    inference: TypeInferenceContext,
}

impl GlobalContext {
    /// Create a new, empty bundle.
    pub fn new() -> Self {
        let mut result = Self {
            lowering: LoweringContext::default(),
            inference: TypeInferenceContext::new(),
        };
        result.register_stdin_source();
        result
    }

    /// Returns the context for lowering
    pub fn lowering_ctx(&mut self) -> &mut LoweringContext {
        &mut self.lowering
    }

    /// Returns the context for type inference
    pub fn inference_ctx(&mut self) -> &mut TypeInferenceContext {
        &mut self.inference
    }

    /// Register a [`TestDataSource`] under `name`.
    ///
    /// The inferred CCL type is `DataSource(name) ⇒ output_type`, where
    /// `output_type` is derived from the source's output extent.
    pub fn register_test_source(&mut self, ds: Rc<RefCell<TestDataSource>>) {
        let name = ds.borrow().get_id().to_string();
        self.lowering.register_source(&name);
        let output_type = ds.borrow().output_type();
        self.inference.register_source_type(
            &name,
            Type::Fun(
                Box::new(Type::DataSource(name.to_string())),
                Box::new(output_type),
            ),
        );
    }

    /// Register a [`StdinDataSource`] under `name`.
    ///
    /// Stdin produces strings, so the inferred CCL type is
    /// `DataSource(name) ⇒ String`.
    pub fn register_stdin_source(&mut self) {
        let name = "__stdinvalues";
        self.lowering.register_source(name);
        self.inference.register_source_type(
            name,
            Type::Fun(
                Box::new(Type::DataSource(name.to_string())),
                Box::new(Type::Base(BaseType::String)),
            ),
        );
    }
}

impl Default for GlobalContext {
    fn default() -> Self {
        Self::new()
    }
}
