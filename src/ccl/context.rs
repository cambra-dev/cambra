// ---------------------------------------------------------------------------
// Context object for state shared across all phases of compilation like
// builtins
// ---------------------------------------------------------------------------

use std::{cell::RefCell, rc::Rc};

use log::debug;
use rustpython_parser::{ast as pyast, parser};

use crate::{
    ccl::{
        infer::{check_fully_typed, infer, typecheck, TypeInferenceContext},
        lambda_elim,
        lower::{lower_stmts, LoweringContext},
        symbolic::{symbolic, symbolic_typed},
        BaseType, Expr, Type,
    },
    interpreter::{
        compile_tile_operators::{compile_tile, TileCompileContext},
        operator_conversion::convert_to_operators,
        tile_operators::{TileOperator, TileProducer},
        Consumer, DataSourceDomainExtentImpl, Scheduler, StdinDataSource, TestDataSource,
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

    /// Compile `code` and return the producer together with pre-rendered tree
    /// strings for the web inspector: `(producer, ccl_repr, operator_tree)`.
    pub fn compile_program_with_trees(
        &mut self,
        code: &str,
        consumer: Box<dyn Consumer>,
    ) -> (Box<dyn TileProducer>, String, String) {
        let result = parser::parse(code, parser::Mode::Module, "<test>")
            .expect("Failed to parse Python module");
        let stmts = match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        };
        let mut expr = lower_stmts(&stmts, self.lowering_ctx()).expect("ccl lowering failed");

        let ctx = self.inference_ctx();
        infer(&mut expr, ctx).expect("type inference failed");

        let ccl_repr = symbolic(&expr);
        debug!("CCL:\n{ccl_repr}");

        let mut op = compile_tile(&expr, self.compile_ctx()).expect("compile failed");

        let operator_tree = pretty_tile_operator(op.as_ref());
        debug!("Operators:\n{operator_tree}");

        let producer = op.subscribe(op.tiling().universal_guard(), consumer, self.scheduler());

        debug!("Producers:\n{}", pretty_tile_producer(producer.as_ref()));

        (producer, ccl_repr, operator_tree)
    }

    /// Compile `code` and return the producer.
    pub fn compile_program(
        &mut self,
        code: &str,
        consumer: Box<dyn Consumer>,
    ) -> Box<dyn TileProducer> {
        self.compile_program_with_trees(code, consumer).0
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
    pub fn compile_ctx(&mut self) -> &mut TileCompileContext {
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

/// Runs as much of the new compilation stack as we have implemented so far.
pub fn new_compile_program(
    ctx: &mut GlobalContext,
    code: &str,
    consumer: Box<dyn Consumer>,
) -> (Expr, Box<dyn TileOperator>, Box<dyn TileProducer>) {
    let result =
        parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse Python module");
    let stmts = match result {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("expected Module, got {other:?}"),
    };
    let mut expr = lower_stmts(&stmts, ctx.lowering_ctx()).expect("ccl lowering failed");

    let infer_ctx = ctx.inference_ctx();
    infer(&mut expr, infer_ctx).expect("type inference failed");

    let ccl_repr = symbolic(&expr);
    debug!("CCL:\n{ccl_repr}");

    let lambda_elim = lambda_elim::run(expr).expect("Lambda elim failed");
    debug!("λ-eliminated CCL:\n{}", symbolic_typed(&lambda_elim));

    debug!("Table:\n{}", ctx.inference_ctx().table);

    check_fully_typed(&lambda_elim).expect("missing types");
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    let mut op =
        convert_to_operators(&lambda_elim, ctx.compile_ctx()).expect("Operator conversion failed");

    let producer = op.subscribe(op.tiling().universal_guard(), consumer, ctx.scheduler());

    debug!("Producers:\n{}", pretty_tile_producer(producer.as_ref()));

    (lambda_elim, op, producer)
}
