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
        inline, join_plan, lambda_elim,
        lower::{lower_stmts, LoweringContext},
        symbolic::{symbolic, symbolic_typed},
        BaseType, Expr, Type,
    },
    interpreter::{
        operator_conversion::{convert_to_operators, OpConversionContext},
        tile_operators::{TileOperator, TileProducer},
        Consumer, DataSourceDomainExtentImpl, Scheduler, StdinDataSource, TestDataSource,
    },
    pretty_graph::{pretty_tile_producer_with, VizOptions},
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
    /// Operator Conversion context.
    conversion: OpConversionContext,
    /// Scheduler for triggering notifications.
    scheduler: Scheduler,
}

impl GlobalContext {
    /// Create a new, empty bundle.
    pub fn new() -> Self {
        let mut result = Self {
            lowering: LoweringContext::default(),
            inference: TypeInferenceContext::new(),
            conversion: OpConversionContext::new(),
            scheduler: Scheduler::new(),
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

    /// Returns the context for operator conversion
    pub fn conversion_ctx(&mut self) -> &mut OpConversionContext {
        &mut self.conversion
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
        self.conversion.register_source(name, ds);
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
        self.conversion.register_source(name, ds);
    }
}

impl Default for GlobalContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Compiles a CHL program to a TileProducer that will produce the output of the program.
/// Returns the final state of the CCL, the TileOperator graph, and the TileProducer graph.
pub fn compile_program(
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
    ctx.lowering_ctx().use_ccl_for_groupby = true;
    let mut expr = lower_stmts(&stmts, ctx.lowering_ctx()).expect("ccl lowering failed");

    debug!("Lowered:\n{}", symbolic(&expr));

    let infer_ctx = ctx.inference_ctx();
    infer(&mut expr, infer_ctx).expect("type inference failed");
    debug!("Inferred:\n{}", symbolic(&expr));
    debug!("Inferred (typed):\n{}", symbolic_typed(&expr));
    typecheck(&expr).expect("Inference created invalid expr");

    // Inline UDFs: substitute both scalar and list-producing UDF Let bindings
    // and beta-reduce at each call site before lambda elimination.  This
    // strips the outer user-parameter lambda from list-producing UDFs so the
    // remaining Lambda layer matches the list-comprehension shape that
    // lambda-elim handles, and avoids a runtime panic when operator conversion
    // would otherwise try to iterate over a scalar's infinite domain.
    let udfs_inlined = inline::inline_non_iterable_lambdas(expr);
    debug!("UDFs inlined CCL:\n{}", symbolic(&udfs_inlined));
    typecheck(&udfs_inlined).expect("type error after UDF inlining");

    let lambda_elim = lambda_elim::run(udfs_inlined).expect("Lambda elim failed");
    debug!("λ-eliminated CCL:\n{}", symbolic(&lambda_elim));
    debug!("λ-eliminated typed CCL:\n{}", symbolic_typed(&lambda_elim));

    check_fully_typed(&lambda_elim).expect("missing types");
    typecheck(&lambda_elim).expect("type error after lambda elimination");

    let join_planned = join_plan::run(lambda_elim);

    debug!(
        "Join-planned CCL:\n{} : {}",
        symbolic(&join_planned),
        join_planned.ty
    );
    debug!("Join-planned CCL:\n{}", symbolic_typed(&join_planned));

    let mut op = convert_to_operators(&join_planned, ctx.conversion_ctx())
        .expect("Operator conversion failed");

    let producer = op.subscribe(op.tiling().universal_guard(), consumer, ctx.scheduler());

    debug!(
        "Producers:\n{}",
        pretty_tile_producer_with(
            producer.as_ref(),
            &VizOptions {
                max_depth: Some(30),
                ..Default::default()
            }
        )
    );

    (join_planned, op, producer)
}
