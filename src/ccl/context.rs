// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::{cell::RefCell, rc::Rc};

use log::debug;
use rustpython_parser::{ast as pyast, parser};

use crate::{
    ccl::{
        infer::{infer, TypeInferenceContext},
        lower::{lower_stmts, LoweringContext},
        symbolic::symbolic,
        Type,
    },
    interpreter::{
        compile_tile_operators::{compile_tile, TileCompileContext},
        tile_operators::TileProducer,
        BaseType, Consumer, DataSourceDomainExtentImpl, Scheduler, StdinDataSource, TestDataSource,
    },
    pretty_graph::{pretty_tile_operator, pretty_tile_producer},
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
    /// Compilation context.
    compile: TileCompileContext,
    /// Scheduler for triggering notifications.
    scheduler: Scheduler,
}

impl GlobalContext {
    /// Create a new, empty bundle.
    pub fn new() -> Self {
        let mut result = Self {
            lowering: LoweringContext::default(),
            inference: TypeInferenceContext::new(),
            compile: TileCompileContext::new(),
            scheduler: Scheduler::new(),
        };
        result.register_stdin_source();
        result
    }

    pub fn compile_program(
        &mut self,
        code: &str,
        consumer: Box<dyn Consumer>,
    ) -> Box<dyn TileProducer> {
        let result = parser::parse(code, parser::Mode::Module, "<test>")
            .expect("Failed to parse Python module");
        let stmts = match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        };
        let mut expr = lower_stmts(&stmts, self.lowering_ctx()).expect("ccl lowering failed");

        let ctx = self.inference_ctx();
        infer(&mut expr, ctx).expect("type inference failed");

        debug!("CCL:\n{}", symbolic(&expr));

        let mut op = compile_tile(&expr, self.compile()).expect("compile failed");

        debug!("Operators:\n{}", pretty_tile_operator(op.as_ref()));

        let producer = op.subscribe(op.tiling().universal_guard(), consumer, self.scheduler());

        debug!("Producers:\n{}", pretty_tile_producer(producer.as_ref()));

        producer
    }

    /// Returns the context for lowering
    pub fn lowering_ctx(&mut self) -> &mut LoweringContext {
        &mut self.lowering
    }

    /// Returns the context for type inference
    pub fn inference_ctx(&mut self) -> &mut TypeInferenceContext {
        &mut self.inference
    }

    /// Returns the context for type inference
    pub fn compile(&mut self) -> &mut TileCompileContext {
        &mut self.compile
    }

    pub fn scheduler(&mut self) -> &mut Scheduler {
        &mut self.scheduler
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
        self.compile.register_source(name, ds);
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
        let ds = Rc::new(RefCell::new(StdinDataSource::new()));
        self.compile.register_source(name, ds);
    }
}

impl Default for GlobalContext {
    fn default() -> Self {
        Self::new()
    }
}
