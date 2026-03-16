//! Python AST → CCL lowering.
//!
//! Translates [`rustpython_parser`] AST nodes into [`crate::ccl::Expr`] trees.
//! This is a structural lowering only — no type inference, no operator-graph
//! construction, and no subscription. The resulting CCL tree can be inspected
//! and tested independently before being type-checked and compiled.
//!
//! # Supported constructs
//!
//! | Python syntax | CCL output |
//! |--------------|-----------|
//! | Integer / string / bool / None literals | [`Expr::Lit`] |
//! | Variable references | [`Expr::Var`] |
//! | Binary arithmetic (`+`, `-`, `*`, `//`) | [`Expr::BinOp`] |
//! | Comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) | [`Expr::BinOp`] |
//! | Chained comparisons (`a < b < c`) | nested [`Expr::BinOp`] with `and` |
//! | Boolean operators (`and`, `or`) | left-folded [`Expr::BinOp`] chain |
//! | List literals `[e0, e1, ...]` | [`Expr::List`] |
//! | Single-generator list comprehensions (no `if`) | `Lambda`/`Apply` encoding |
//! | 2-gen equality-join comprehensions (`if x.k == y.k`) | hash-join [`crate::ccl::RefinementKind::HashJoin`] |
//! | Multi-gen filtered comprehensions (non-equality or 3+ generators) | loop-join [`crate::ccl::RefinementKind::Predicate`] |
//! | Assignment + expression blocks | nested [`Expr::Let`] |
//! | `sum(expr)` / `max(expr)` calls | [`Expr::Aggregate`] |
//! | Lambda expressions `lambda x: body` | curried [`Expr::Lambda`] chain |
//! | `groupby(collection, key)` calls | [`Expr::GroupBy`] |
//!
//! Everything else returns [`LoweringError::Unsupported`].
//!
//! # Name uniqueness
//!
//! This pass does not guarantee unique binding names. Python reassignment of the
//! same variable (`x = 1; x = 2`) produces nested [`Expr::Let`] nodes that shadow
//! each other (`let x = 1 in let x = 2 in ...`). The semantics are correct for
//! sequential code — the inner `let` evaluates its value expression in the outer
//! scope before the shadowing takes effect — but the same name may appear at
//! multiple binding sites in the resulting tree.
//!
//! Unlike SSA or ANF form, CCL does not α-rename each assignment to a fresh variable.
//! This is intentional: the less-normalized representation preserves structure
//! needed for optimization passes.

use std::{collections::HashSet, rc::Rc};

use bit_set::BitSet;
use rustpython_parser::ast as pyast;

use crate::ccl::{
    AggregateKind, ArithmeticKind, BinOpKind, CompareKind, Expr, HashJoinSpec, Lit, LogicKind,
    Type, TypedBinding,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during Python → CCL lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum LoweringError {
    /// The AST node or construct is not yet supported by this lowering pass.
    Unsupported(String),
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

/// Context for Python → CCL lowering that carries externally-registered source names.
///
/// Zero-argument function calls whose name is registered here are lowered to
/// [`crate::ccl::Expr::Source`] nodes instead of failing with an
/// [`LoweringError::Unsupported`] error. The caller is responsible for
/// registering the matching type in [`crate::ccl::infer::TypeInferenceContext`]
/// and operator factory in [`crate::interpreter::compile_ccl::CompileContext`]
/// before running those passes.
#[derive(Default)]
pub struct LoweringContext {
    known_sources: HashSet<String>,
}

impl LoweringContext {
    /// Register `name` as a known data-source call (e.g. `"testsource1"`,
    /// `"__stdinvalues"`).
    pub fn register_source(&mut self, name: &str) {
        self.known_sources.insert(name.to_string());
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Lower a single Python expression to a CCL expression.
pub fn lower_expr(
    expr: &pyast::Located<pyast::ExprKind>,
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    match &expr.node {
        pyast::ExprKind::Constant { value, .. } => lower_constant(value),
        pyast::ExprKind::Name { id, .. } => Ok(Expr::Var(id.clone())),
        pyast::ExprKind::BinOp { left, op, right } => lower_binop(left, op, right, ctx),
        pyast::ExprKind::Compare {
            left,
            ops,
            comparators,
        } => lower_compare(left, ops, comparators, ctx),
        pyast::ExprKind::BoolOp { op, values } => lower_boolop(op, values, ctx),
        pyast::ExprKind::List { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::List(items?))
        }
        pyast::ExprKind::ListComp { elt, generators } => lower_list_comp(elt, generators, ctx),
        pyast::ExprKind::Call {
            func,
            args,
            keywords,
        } => lower_call(func, args, keywords, ctx),
        pyast::ExprKind::Tuple { elts, .. } => {
            let items: Result<Vec<_>, _> = elts.iter().map(|e| lower_expr(e, ctx)).collect();
            Ok(Expr::Tuple(items?))
        }
        pyast::ExprKind::Subscript { value, slice, .. } => match &slice.node {
            pyast::ExprKind::Constant {
                value: pyast::Constant::Int(n),
                ..
            } => {
                let idx: usize = n.try_into().map_err(|_| {
                    LoweringError::Unsupported("Tuple index must be non-negative".into())
                })?;
                Ok(Expr::TupleIndex(Box::new(lower_expr(value, ctx)?), idx))
            }
            _ => Err(LoweringError::Unsupported(
                "Only integer subscripts are supported".into(),
            )),
        },
        pyast::ExprKind::Lambda { args, body } => lower_lambda(args, body, ctx),
        _ => Err(LoweringError::Unsupported(format!(
            "Expression type not supported: {:?}",
            expr.node
        ))),
    }
}

/// Lower a block of Python statements to a nested CCL expression.
///
/// All statements except the last must be simple name assignments
/// (`x = expr`); each becomes an [`Expr::Let`] binding wrapping the rest.
/// The last statement must be a bare expression (`StmtKind::Expr`).
pub fn lower_stmts(stmts: &[pyast::Stmt], ctx: &LoweringContext) -> Result<Expr, LoweringError> {
    if stmts.is_empty() {
        return Err(LoweringError::Unsupported("Empty statement block".into()));
    }

    let (last, rest) = stmts.split_last().unwrap();

    // The final statement must be a bare expression.
    let final_expr = match &last.node {
        pyast::StmtKind::Expr { value } => lower_expr(value, ctx)?,
        _ => {
            return Err(LoweringError::Unsupported(
                "Last statement must be a bare expression".into(),
            ))
        }
    };

    // Wrap preceding assignments in Let bindings, innermost-first.
    rest.iter()
        .rev()
        .try_fold(final_expr, |body, stmt| match &stmt.node {
            pyast::StmtKind::Assign { targets, value, .. } => {
                if targets.len() != 1 {
                    return Err(LoweringError::Unsupported(
                        "Multiple assignment targets not supported".into(),
                    ));
                }
                let name = match &targets[0].node {
                    pyast::ExprKind::Name { id, .. } => id.clone(),
                    _ => {
                        return Err(LoweringError::Unsupported(
                            "Destructuring assignment not supported".into(),
                        ))
                    }
                };
                let val = lower_expr(value, ctx)?;
                Ok(Expr::Let {
                    binding: TypedBinding::new_unannotated(&name),
                    bound_expr: Box::new(val),
                    body: Box::new(body),
                })
            }
            _ => Err(LoweringError::Unsupported(
                "Only assignment statements are supported before the final expression".into(),
            )),
        })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn lower_constant(constant: &pyast::Constant) -> Result<Expr, LoweringError> {
    let lit = match constant {
        pyast::Constant::Int(n) => {
            let n_i64: i64 = n
                .try_into()
                .map_err(|_| LoweringError::Unsupported("Integer too large for i64".into()))?;
            Lit::Int(n_i64)
        }
        pyast::Constant::Str(s) => Lit::String(s.clone()),
        pyast::Constant::Bool(b) => Lit::Bool(*b),
        pyast::Constant::None => Lit::Unit,
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Constant type not supported: {constant:?}"
            )))
        }
    };
    Ok(Expr::Lit(lit))
}

/// Lower a Python function call to a CCL built-in expression.
///
/// Supported built-ins:
///
/// | Python call | CCL node | Arity |
/// |---|---|---|
/// | `sum(expr)` | [`Expr::Aggregate`] (`Sum`) | 1 |
/// | `max(expr)` | [`Expr::Aggregate`] (`Max`) | 1 |
/// | `groupby(collection, key)` | [`Expr::GroupBy`] | 2 |
///
/// Keyword arguments and unknown function names return
/// [`LoweringError::Unsupported`].
fn lower_call(
    func: &pyast::Expr,
    args: &[pyast::Expr],
    keywords: &[pyast::Keyword],
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    if !keywords.is_empty() {
        return Err(LoweringError::Unsupported(
            "Keyword arguments not supported in function calls".into(),
        ));
    }
    let name = match &func.node {
        pyast::ExprKind::Name { id, .. } => id.as_str(),
        _ => {
            return Err(LoweringError::Unsupported(
                "Only named function calls are supported".into(),
            ))
        }
    };

    match name {
        "groupby" => {
            if args.len() != 2 {
                return Err(LoweringError::Unsupported(
                    "groupby requires exactly two arguments".into(),
                ));
            }
            let collection = lower_expr(&args[0], ctx)?;
            let key = lower_expr(&args[1], ctx)?;
            Ok(Expr::GroupBy {
                collection: Box::new(collection),
                key: Box::new(key),
            })
        }
        "sum" | "max" => {
            if args.len() != 1 {
                return Err(LoweringError::Unsupported(
                    "Aggregate functions require exactly one argument".into(),
                ));
            }
            let kind = match name {
                "sum" => AggregateKind::Sum,
                "max" => AggregateKind::Max,
                _ => unreachable!(),
            };
            let input = lower_expr(&args[0], ctx)?;
            Ok(Expr::Aggregate {
                input: Box::new(input),
                kind,
            })
        }
        name if ctx.known_sources.contains(name) => Ok(Expr::Source(name.to_string())),
        _ => Err(LoweringError::Unsupported(format!(
            "Unknown function: {name}"
        ))),
    }
}

fn lower_binop(
    left: &pyast::Located<pyast::ExprKind>,
    op: &pyast::Operator,
    right: &pyast::Located<pyast::ExprKind>,
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    let left_expr = lower_expr(left, ctx)?;
    let right_expr = lower_expr(right, ctx)?;
    let kind = match op {
        pyast::Operator::Add => BinOpKind::Arithmetic(ArithmeticKind::Add),
        pyast::Operator::Sub => BinOpKind::Arithmetic(ArithmeticKind::Sub),
        pyast::Operator::Mult => BinOpKind::Arithmetic(ArithmeticKind::Mul),
        pyast::Operator::FloorDiv => BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
        pyast::Operator::BitAnd => BinOpKind::BoolLogic(LogicKind::And),
        pyast::Operator::BitOr => BinOpKind::BoolLogic(LogicKind::Or),
        pyast::Operator::BitXor => BinOpKind::BoolLogic(LogicKind::Xor),
        _ => {
            return Err(LoweringError::Unsupported(format!(
                "Binary operator not supported: {op:?}"
            )))
        }
    };
    Ok(Expr::BinOp {
        left: Box::new(left_expr),
        op: kind,
        right: Box::new(right_expr),
    })
}

/// Lower a Python comparison expression to a CCL [`Expr::BinOp`] chain.
///
/// Python comparison expressions may chain multiple operators, e.g. `a < b < c`
/// desugars to `a < b and b < c`. Each consecutive pair of operands is compared
/// with its corresponding operator and the results are combined with logical AND.
///
/// Unsupported operators (`is`, `is not`, `in`, `not in`) return
/// [`LoweringError::Unsupported`].
fn lower_compare(
    left: &pyast::Located<pyast::ExprKind>,
    ops: &[pyast::Cmpop],
    comparators: &[pyast::Located<pyast::ExprKind>],
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    // Lower all operands up-front. For a chain of n ops there are n+1 operands:
    // left, comparators[0], comparators[1], …
    let mut operands: Vec<Expr> = Vec::with_capacity(comparators.len() + 1);
    operands.push(lower_expr(left, ctx)?);
    for comp in comparators {
        operands.push(lower_expr(comp, ctx)?);
    }

    // Build one BinOp per (op, adjacent-operand-pair).
    let mut comparisons: Vec<Expr> = Vec::with_capacity(ops.len());
    for (i, op) in ops.iter().enumerate() {
        let kind = match op {
            pyast::Cmpop::Eq => CompareKind::Equals,
            pyast::Cmpop::NotEq => CompareKind::NotEquals,
            pyast::Cmpop::Lt => CompareKind::Less,
            pyast::Cmpop::LtE => CompareKind::LessOrEq,
            pyast::Cmpop::Gt => CompareKind::Greater,
            pyast::Cmpop::GtE => CompareKind::GreaterOrEq,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Comparison operator not supported: {op:?}"
                )))
            }
        };
        // Clone the shared middle operand so both adjacent pairs can own it.
        comparisons.push(Expr::BinOp {
            left: Box::new(operands[i].clone()),
            op: BinOpKind::Compare(kind),
            right: Box::new(operands[i + 1].clone()),
        });
    }

    // Single comparison: return it directly.
    // Chained comparisons: fold with logical AND (mirrors Python semantics).
    Ok(comparisons
        .into_iter()
        .reduce(|acc, cmp| Expr::BinOp {
            left: Box::new(acc),
            op: BinOpKind::BoolLogic(LogicKind::And),
            right: Box::new(cmp),
        })
        .expect("ops is non-empty"))
}

/// Lower a Python boolean operator expression to a left-folded [`Expr::BinOp`] chain.
///
/// Python `BoolOp` carries a list of two or more operands sharing a single
/// operator (`and` / `or`). For example, `a and b and c` becomes
/// `(a and b) and c` — two nested [`BinOpKind::BoolLogic`] nodes.
fn lower_boolop(
    op: &pyast::Boolop,
    values: &[pyast::Located<pyast::ExprKind>],
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    if values.len() < 2 {
        return Err(LoweringError::Unsupported(
            "Boolean operator must have at least two operands".into(),
        ));
    }
    let kind = match op {
        pyast::Boolop::And => BinOpKind::BoolLogic(LogicKind::And),
        pyast::Boolop::Or => BinOpKind::BoolLogic(LogicKind::Or),
    };
    // Fold left-to-right: `a and b and c` → `(a and b) and c`.
    let mut acc = lower_expr(&values[0], ctx)?;
    for value in &values[1..] {
        acc = Expr::BinOp {
            left: Box::new(acc),
            op: kind.clone(),
            right: Box::new(lower_expr(value, ctx)?),
        };
    }
    Ok(acc)
}

// ---------------------------------------------------------------------------
// Join-detection helpers (operate on the lowered CCL AST)
// ---------------------------------------------------------------------------

/// Compute the set of generator-variable indices referenced anywhere in a CCL [`Expr`].
///
/// Returns a [`BitSet`] where bit `i` is set when `expr` contains a [`Expr::Var`]
/// whose name matches `gen_var_names[i]`.
fn ccl_gen_vars_referenced(expr: &Expr, gen_var_names: &[&str]) -> BitSet {
    let mut result = BitSet::new();
    let mut shadowed = BitSet::new();
    ccl_gen_vars_referenced_inner(expr, gen_var_names, &mut result, &mut shadowed);
    result
}

fn ccl_gen_vars_referenced_inner(
    expr: &Expr,
    gen_var_names: &[&str],
    result: &mut BitSet,
    shadowed: &mut BitSet,
) {
    match expr {
        Expr::Var(name) => {
            if let Some(i) = gen_var_names.iter().position(|n| *n == name.as_str()) {
                // TODO once we support lambda expressions in CHL, test that the shadowing here
                // actually works.
                if !shadowed.contains(i) {
                    result.insert(i);
                }
            }
        }
        Expr::BinOp { left, right, .. } => {
            ccl_gen_vars_referenced_inner(left, gen_var_names, result, shadowed);
            ccl_gen_vars_referenced_inner(right, gen_var_names, result, shadowed);
        }
        Expr::UnaryOp(_, operand) => {
            ccl_gen_vars_referenced_inner(operand, gen_var_names, result, shadowed);
        }
        Expr::Apply { function, argument } => {
            ccl_gen_vars_referenced_inner(function, gen_var_names, result, shadowed);
            ccl_gen_vars_referenced_inner(argument, gen_var_names, result, shadowed);
        }
        Expr::Lambda { body, param, .. } => {
            // Generator variables are free in the predicate; descend into body.
            let outer_shadowed = shadowed.clone();
            if let Some(i) = gen_var_names.iter().position(|n| *n == param.name) {
                shadowed.insert(i);
            }
            ccl_gen_vars_referenced_inner(body, gen_var_names, result, shadowed);
            *shadowed = outer_shadowed;
        }
        Expr::Let {
            binding,
            bound_expr,
            body,
        } => {
            ccl_gen_vars_referenced_inner(bound_expr, gen_var_names, result, shadowed);
            let outer_shadowed = shadowed.clone();
            if let Some(i) = gen_var_names.iter().position(|n| *n == binding.name) {
                shadowed.insert(i);
            }
            ccl_gen_vars_referenced_inner(body, gen_var_names, result, shadowed);
            *shadowed = outer_shadowed;
        }
        Expr::List(items) | Expr::Tuple(items) => {
            for item in items {
                ccl_gen_vars_referenced_inner(item, gen_var_names, result, shadowed);
            }
        }
        Expr::TupleIndex(expr, _) => {
            ccl_gen_vars_referenced_inner(expr, gen_var_names, result, shadowed);
        }
        Expr::TypeAnnotation(expr, _) => {
            ccl_gen_vars_referenced_inner(expr, gen_var_names, result, shadowed);
        }
        Expr::GroupBy { collection, key } => {
            ccl_gen_vars_referenced_inner(collection, gen_var_names, result, shadowed);
            ccl_gen_vars_referenced_inner(key, gen_var_names, result, shadowed);
        }
        Expr::Lit(_) => {}
        _ => {}
    }
}

/// If `pred` is a CCL equality between expressions each referencing a distinct
/// single generator variable, return `(build_gen, build_key, probe_gen, probe_key)`
/// normalised so that `build_gen < probe_gen`.
///
/// Returns `None` for any other predicate shape.
fn try_extract_ccl_equality_join<'a>(
    pred: &'a Expr,
    gen_var_names: &[&str],
) -> Option<(usize, &'a Expr, usize, &'a Expr)> {
    if let Expr::BinOp {
        left,
        op: BinOpKind::Compare(CompareKind::Equals),
        right,
    } = pred
    {
        let refs_lhs = ccl_gen_vars_referenced(left, gen_var_names);
        let refs_rhs = ccl_gen_vars_referenced(right, gen_var_names);
        if refs_lhs.len() == 1 && refs_rhs.len() == 1 {
            let gen_l = refs_lhs.iter().next().unwrap();
            let gen_r = refs_rhs.iter().next().unwrap();
            if gen_l != gen_r {
                // Normalise: smaller generator index = build side.
                return if gen_l < gen_r {
                    Some((gen_l, left, gen_r, right))
                } else {
                    Some((gen_r, right, gen_l, left))
                };
            }
        }
    }
    None
}

/// Lower a Python lambda expression to a curried [`Expr::Lambda`] chain.
///
/// Each positional parameter becomes one lambda layer, outermost-first, so
/// `lambda x, y: x + y` lowers to `λ x → λ y → x + y`.
///
/// Unsupported features (`*args`, `**kwargs`, default values, keyword-only
/// arguments) return [`LoweringError::Unsupported`].
fn lower_lambda(
    args: &pyast::Arguments,
    body: &pyast::Located<pyast::ExprKind>,
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    if args.vararg.is_some() {
        return Err(LoweringError::Unsupported(
            "Lambda *args not supported".into(),
        ));
    }
    if args.kwarg.is_some() {
        return Err(LoweringError::Unsupported(
            "Lambda **kwargs not supported".into(),
        ));
    }
    if !args.kwonlyargs.is_empty() {
        return Err(LoweringError::Unsupported(
            "Lambda keyword-only arguments not supported".into(),
        ));
    }
    if !args.defaults.is_empty() {
        return Err(LoweringError::Unsupported(
            "Lambda default arguments not supported".into(),
        ));
    }
    if args.args.is_empty() {
        // TODO do we need to support 0-arg lambdas?
        return Err(LoweringError::Unsupported(
            "Lambda with no parameters not supported".into(),
        ));
    }

    // Lower the body once; then wrap it in one lambda per parameter,
    // innermost-first (reverse order) to produce the curried chain.
    let body_expr = lower_expr(body, ctx)?;
    let result = args.args.iter().rev().fold(body_expr, |acc, arg| {
        Expr::lambda(&arg.node.arg, Type::Unknown, acc)
    });
    Ok(result)
}

/// Lower a Python list comprehension to the CCL Lambda/Apply encoding.
///
/// Handles three cases based on the number of generators and predicates:
///
/// **Single generator, no predicate** — identity encoding:
/// ```text
/// λ __iter_record → __iter_record ▷ lower(source) ▷ (λ var → lower(body))
/// ```
///
/// **Multiple generators / non-equality predicates** — loop-join encoding.
/// The outer lambda carries a [`RefinementKind::Predicate`] with the combined
/// guard expression; the runtime filters via a correlation vector:
/// ```text
/// λ __iter_record : {T | Refined(pred)} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// **Two generators, single equality predicate** — hash-join encoding.
/// Detected by [`try_extract_ccl_equality_join`] on the lowered predicate.
/// The outer lambda carries a [`RefinementKind::HashJoin`]; `compile_ccl`
/// translates it to an O(N+M) hash-join-based restriction:
/// ```text
/// λ __iter_record : {T | Refined(build_var == probe_var)} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// All lambdas are produced with `param.ty = Type::Unknown`; [`crate::ccl::infer`]
/// fills in the type annotations before compilation.
///
/// TODO this currently has an assumption that all generator variables have distinct names.
/// This might be a reasonable assumption that we should enforce, or we should fix scoping to
/// handle that case.
fn lower_list_comp(
    elt: &pyast::Located<pyast::ExprKind>,
    generators: &[pyast::Comprehension],
    ctx: &LoweringContext,
) -> Result<Expr, LoweringError> {
    // ---- Phase 1: Lower each generator's source and register its loop variable ----
    // We keep the source operators and index extents for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut gen_iter_vars: Vec<String> = Vec::new();

    for gen in generators.iter() {
        if gen.is_async > 0 {
            return Err(LoweringError::Unsupported(
                "Async comprehensions are not supported".into(),
            ));
        }
        let source = lower_expr(&gen.iter, ctx)?;
        let var_name = match &gen.target.node {
            pyast::ExprKind::Name { id, .. } => id,
            _ => {
                return Err(LoweringError::Unsupported(format!(
                    "Only simple variable targets are supported in comprehensions, got {:?}",
                    gen.target.node
                )));
            }
        };
        let iter_var = var_name;
        gen_iter_vars.push(iter_var.to_string());
        gen_sources.push(source);
    }

    // ---- Phase 2: Lower body and all predicates to CCL -------------------------
    let body = lower_expr(elt, ctx)?;

    // Lower every `if` guard from each generator to CCL.  We hold on to the
    // original pyast nodes only to build human-readable description strings;
    // all detection logic operates on the lowered CCL expressions.
    let pyast_preds: Vec<&pyast::Expr> = generators
        .iter()
        .flat_map(|g| g.ifs.iter().map(|e| e as &pyast::Expr))
        .collect();
    let lowered_preds: Vec<Expr> = pyast_preds
        .iter()
        .map(|e| lower_expr(e, ctx))
        .collect::<Result<_, _>>()?;

    let gen_var_refs: Vec<&str> = gen_iter_vars.iter().map(String::as_str).collect();

    // Detect a 2-generator equality join on the CCL AST: exactly 2 generators,
    // 1 predicate, and the predicate is `lhs == rhs` where each side references
    // a distinct generator variable.  Emit a hash-join refinement instead of a
    // loop-join predicate.  Sources are cloned from the already-lowered
    // `gen_sources`; key expressions are taken directly from the lowered predicate.
    // TODO move this to a later phase of compilation.
    let hash_join_spec: Option<HashJoinSpec> = if generators.len() == 2 && lowered_preds.len() == 1
    {
        if let Some((build_gen, build_key, probe_gen, probe_key)) =
            try_extract_ccl_equality_join(&lowered_preds[0], &gen_var_refs)
        {
            Some(HashJoinSpec {
                build_gen_position: build_gen,
                probe_gen_position: probe_gen,
                build_var_name: gen_iter_vars[build_gen].clone(),
                probe_var_name: gen_iter_vars[probe_gen].clone(),
                build_key: Rc::new(build_key.clone()),
                probe_key: Rc::new(probe_key.clone()),
                build_source: Rc::new(gen_sources[build_gen].clone()),
                probe_source: Rc::new(gen_sources[probe_gen].clone()),
            })
        } else {
            None
        }
    } else {
        None
    };

    // Combine all `if` guards into a single loop-join predicate (used when hash
    // join is not applicable — non-equality, 3+ generators, or multiple predicates).
    // Description strings are built from the original pyast Display output.
    let mut pred_op: Option<Expr> = None;
    let mut pred_desc = String::new();
    if hash_join_spec.is_none() {
        for (pyast_pred, lowered) in pyast_preds.iter().zip(lowered_preds) {
            pred_op = Some(match pred_op {
                Some(lhs) => {
                    pred_desc.push_str(&format!(" and {pyast_pred}"));
                    Expr::BinOp {
                        left: Box::new(lhs),
                        op: BinOpKind::BoolLogic(LogicKind::And),
                        right: Box::new(lowered),
                    }
                }
                None => {
                    pred_desc = format!("{pyast_pred}");
                    lowered
                }
            });
        }
    }

    // Sources for the loop-join restriction lambda are cloned from the
    // already-lowered gen_sources (Phase 5 drains it, so clone here).
    let mut pred_sources: Vec<Expr> = if pred_op.is_some() {
        gen_sources.clone()
    } else {
        Vec::new()
    };

    // ---- Phase 4: Build the outer iteration variable ------------------------------
    // Single generator: iterate directly over that source's index extent.
    // Multiple generators: pack all index extents into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a predicate: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see Phase 6).
    let single_gen = generators.len() == 1;
    let outer_var = "__iter_record";

    // Helper: build the index argument for generator `i`.
    // Single-gen: a bare VarRef to the outer variable.
    // Multi-gen: a RecordField projection of the i-th field from the outer record.
    let make_idx_arg = |var: &str, i: usize| -> Expr {
        let vref = Expr::Var(var.to_string());
        if single_gen {
            vref
        } else {
            Expr::TupleIndex(Box::new(vref), i)
        }
    };

    // ---- Phase 5: Build the body as a nested Apply/Lambda chain ------------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    let mut body_expr: Expr = body;
    for (i, (iter_var, source)) in gen_iter_vars
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        body_expr = Expr::apply(
            Expr::apply(make_idx_arg(outer_var, i), source),
            Expr::lambda(iter_var, Type::Unknown, body_expr),
        );
    }

    // ---- Phase 6: Attach restriction (hash join or loop-join predicate) ----------
    if let Some(spec) = hash_join_spec {
        // Equality join between two generators: emit a hash-join refinement.
        // compile_ccl will construct the Converse/Lambda/Apply operator structure.
        let desc = format!("{} == {}", spec.build_var_name, spec.probe_var_name);
        Ok(Expr::lambda_with_hash_join(
            outer_var,
            Type::Unknown,
            body_expr,
            spec,
            &desc,
        ))
    } else if let Some(pred_op) = pred_op {
        // Non-equality or multi-predicate: loop-join restriction lambda.
        // Uses an independent "__iter_record_restr" variable so it does not
        // recursively depend on a correlation vector.
        let restr_outer_var = "__iter_record_restr";
        let mut pred_expr: Expr = pred_op;
        for (i, (iter_var, pred_source)) in gen_iter_vars
            .iter()
            .zip(pred_sources.drain(..))
            .enumerate()
            .rev()
        {
            pred_expr = Expr::apply(
                Expr::apply(make_idx_arg(restr_outer_var, i), pred_source),
                Expr::lambda(iter_var, Type::Unknown, pred_expr),
            );
        }
        Ok(Expr::lambda_with_refinement(
            outer_var,
            Type::Unknown,
            body_expr,
            Expr::lambda(restr_outer_var, Type::Unknown, pred_expr),
            &pred_desc,
        ))
    } else {
        Ok(Expr::lambda(outer_var, Type::Unknown, body_expr))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{symbolic::symbolic, RefinementKind};
    use rstest::rstest;
    use rustpython_parser::parser;

    /// Parse a Python expression and return the AST node.
    fn parse_expr(code: &str) -> pyast::Expr {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse expression");
        match result {
            pyast::Mod::Expression { body } => *body,
            other => panic!("expected Expression, got {other:?}"),
        }
    }

    /// Parse a Python module and return the statement list.
    fn parse_module(code: &str) -> Vec<pyast::Stmt> {
        let result =
            parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse module");
        match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Single-expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Literals
    #[case("2", "2")]
    #[case(r#""hi""#, r#""hi""#)]
    #[case("True", "true")]
    #[case("None", "unit")]
    // Variable
    #[case("x", "x")]
    // Arithmetic
    #[case("2 + 3", "2 + 3")]
    #[case("4 * 5", "4 * 5")]
    #[case("4 - 5", "4 - 5")]
    #[case("7 // 2", "7 // 2")]
    // Nested binop: `1 + 2 * 3` parses as `1 + (2 * 3)` — * tighter, no parens needed
    #[case("1 + 2 * 3", "1 + 2 * 3")]
    // List literals
    #[case("[]", "[]")]
    #[case("[1, 2]", "[1, 2]")]
    // Comparisons
    #[case("x == 1", "x == 1")]
    #[case("x != 1", "x != 1")]
    #[case("x < 1", "x < 1")]
    #[case("x <= 1", "x <= 1")]
    #[case("x > 1", "x > 1")]
    #[case("x >= 1", "x >= 1")]
    // Chained comparison: `1 < x < 10` → `(1 < x) and (x < 10)`
    #[case("1 < x < 10", "1 < x and x < 10")]
    // Boolean operators
    #[case("x and y", "x and y")]
    #[case("x or y", "x or y")]
    // Three operands fold left: `a and b and c` → `(a and b) and c`
    #[case("a and b and c", "a and b and c")]
    #[case("a or b or c", "a or b or c")]
    // Mixed: `x == 1 and y == 2`
    #[case("x == 1 and y == 2", "x == 1 and y == 2")]
    // Lambdas
    #[case("lambda x: x + 1", "λ x → x + 1")]
    #[case("lambda x, y: x + y", "λ x → λ y → x + y")]
    fn test_lower_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Statement block tests (let bindings)
    // -----------------------------------------------------------------------

    #[rstest]
    #[case(
        "\
x = 2
x",
        "\
let x = 2
in x"
    )]
    #[case(
        "\
x = 2
y = x
y",
        "\
let x = 2
in let y = x
in y"
    )]
    #[case(
        "\
x = 2 + 3
y = x * 4
y",
        "\
let x = 2 + 3
in let y = x * 4
in y"
    )]
    // Note: SSA and ANF disallow this sort of redefinition; our less-normalised
    // representation allows shadowing the same binding name.
    #[case(
        "\
x = 2 + 3
x = x * 4
x",
        "\
let x = 2 + 3
in let x = x * 4
in x"
    )]
    fn test_lower_stmts(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // List comprehension tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Identity: element passes through unchanged; lambdas are unannotated (infer fills them in).
    #[case(
        "[x for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)"
    )]
    // Constant body: loop variable unused in body.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → 42)"
    )]
    // BinOp body: loop variable used in arithmetic.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    // Outer capture: y is captured from an enclosing let binding.
    #[case(
        "\
y = 5
[x + y for x in [10, 20]]",
        "\
let y = 5
in λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + y)"
    )]
    // Nested comprehension: all lambdas unannotated; infer annotates them in a
    // subsequent pass.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __iter_record → __iter_record ▷ (λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)) ▷ (λ y → y)"
    )]
    fn test_lower_list_comp(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Hash join detection tests
    // -----------------------------------------------------------------------

    /// Verify that a 2-generator equality join produces a `RefinementKind::HashJoin`
    /// and a non-equality predicate produces `RefinementKind::Predicate`.
    #[test]
    fn test_hash_join_kind_detection() {
        // Equality join: `x == y` should give HashJoin
        let eq_join = parse_module("[x for x in [1, 2] for y in [3, 4] if x == y]");
        let eq_ccl = lower_stmts(&eq_join, &LoweringContext::default()).expect("lowering failed");
        if let Expr::Lambda { refinement, .. } = &eq_ccl {
            let r = refinement
                .as_ref()
                .expect("expected refinement for equality join");
            assert!(
                matches!(r.kind, RefinementKind::HashJoin(_)),
                "expected HashJoin refinement for `x == y`, got Predicate"
            );
        } else {
            panic!("expected Lambda at top level, got {eq_ccl:?}");
        }

        // Non-equality predicate: `x < y` should give Predicate (loop join)
        let non_eq = parse_module("[x for x in [1, 2] for y in [3, 4] if x < y]");
        let non_eq_ccl =
            lower_stmts(&non_eq, &LoweringContext::default()).expect("lowering failed");
        if let Expr::Lambda { refinement, .. } = &non_eq_ccl {
            let r = refinement
                .as_ref()
                .expect("expected refinement for loop join");
            assert!(
                matches!(r.kind, RefinementKind::Predicate(_)),
                "expected Predicate refinement for `x < y`, got HashJoin"
            );
        } else {
            panic!("expected Lambda at top level, got {non_eq_ccl:?}");
        }
    }

    /// Symbolic output for a 2-gen equality join includes `Refined(x == y)` in the header.
    #[test]
    fn test_hash_join_symbolic() {
        let stmts = parse_module("[x for x in [1, 2] for y in [3, 4] if x == y]");
        let ccl = lower_stmts(&stmts, &LoweringContext::default()).expect("lowering failed");
        let sym = symbolic(&ccl);
        assert!(
            sym.contains("Refined(x == y)"),
            "expected 'Refined(x == y)' in symbolic output, got: {sym}"
        );
    }

    // -----------------------------------------------------------------------
    // Aggregate expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // sum over a list literal
    #[case("sum([1, 2, 3])", "Sum([1, 2, 3])")]
    // max over a list literal
    #[case("max([1, 2])", "Max([1, 2])")]
    // sum over a variable (the input expression is itself a CCL expression)
    #[case("sum(xs)", "Sum(xs)")]
    // max over a variable
    #[case("max(xs)", "Max(xs)")]
    // sum over a list comprehension — input becomes a lambda
    #[case(
        "sum([x for x in [10, 20]])",
        "Sum(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x))"
    )]
    // max over a list comprehension with a body expression
    #[case(
        "max([x + 1 for x in [10, 20]])",
        "Max(λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 1))"
    )]
    fn test_lower_aggregate(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // GroupBy tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Variable collection and inline key lambda
    #[case("groupby(xs, lambda x: x)", "GroupBy(xs, λ x → x)")]
    // List literal collection with a more complex key
    #[case(
        "groupby([1, 2, 3], lambda x: x // 2)",
        "GroupBy([1, 2, 3], λ x → x // 2)"
    )]
    // Key is a variable reference (pre-defined function)
    #[case("groupby(xs, key_fn)", "GroupBy(xs, key_fn)")]
    // Keyed aggregation
    #[case(
        "[sum(x) for x in groupby(xs, key_fn)]",
        "λ __iter_record → __iter_record ▷ GroupBy(xs, key_fn) ▷ (λ x → Sum(x))"
    )]
    fn test_lower_groupby(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// `groupby` with the wrong number of arguments returns `LoweringError::Unsupported`.
    #[test]
    fn test_lower_groupby_wrong_arity() {
        let one_arg = parse_expr("groupby(xs)");
        assert!(matches!(
            lower_expr(&one_arg, &LoweringContext::default()),
            Err(LoweringError::Unsupported(_))
        ));
        let three_args = parse_expr("groupby(xs, f, extra)");
        assert!(matches!(
            lower_expr(&three_args, &LoweringContext::default()),
            Err(LoweringError::Unsupported(_))
        ));
    }

    /// Unsupported call targets produce a `LoweringError::Unsupported`.
    #[test]
    fn test_lower_unknown_function() {
        let expr = parse_expr("foo(x)");
        let err =
            lower_expr(&expr, &LoweringContext::default()).expect_err("expected lowering error");
        assert!(
            matches!(err, LoweringError::Unsupported(_)),
            "expected Unsupported, got {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Source lowering tests
    // -----------------------------------------------------------------------

    /// A zero-argument call whose name is registered lowers to `Expr::Source`.
    #[test]
    fn test_lower_registered_source_becomes_source_node() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream");
        let expr = parse_expr("mystream()");
        let ccl = lower_expr(&expr, &ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "source(mystream)");
    }

    /// A zero-argument call whose name is NOT registered still fails.
    #[test]
    fn test_lower_unregistered_zero_arg_call_fails() {
        let expr = parse_expr("unknown_source()");
        let err =
            lower_expr(&expr, &LoweringContext::default()).expect_err("expected lowering error");
        assert!(matches!(err, LoweringError::Unsupported(_)));
    }

    /// A registered source name used as a non-call expression (plain variable)
    /// lowers to `Expr::Var`, not `Expr::Source` — the call syntax is required.
    #[test]
    fn test_lower_source_name_without_call_is_var() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("mystream");
        let expr = parse_expr("mystream");
        let ccl = lower_expr(&expr, &ctx).expect("lowering failed");
        assert_eq!(symbolic(&ccl), "mystream");
    }

    /// A source call nested inside a larger expression lowers correctly.
    #[test]
    fn test_lower_source_in_list_comp() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("src");
        let stmts = parse_module("[x for x in src()]");
        let ccl = lower_stmts(&stmts, &ctx).expect("lowering failed");
        // The source node should appear in the symbolic output.
        assert!(
            symbolic(&ccl).contains("source(src)"),
            "expected source(src) in output, got: {}",
            symbolic(&ccl)
        );
    }

    // -----------------------------------------------------------------------
    // Future construct tests — ignored until lowering is implemented.
    //
    // These are CHL expressions that will produce Expr::Let nodes in value
    // position once supported. They must be promoted to end-to-end pipeline
    // tests (CHL → CCL → Operators) at that point, as compile_case and any
    // other new compile_* function must save/restore ctx.scope to uphold the
    // invariant described in compile_ccl::compile_let.
    // -----------------------------------------------------------------------

    /// `if/else` with branch-local variables lowers to
    /// `let result = case cond of { True → let tmp = … in … | False → let tmp = … in … } in result`.
    /// The Case branches each contain a Let, so compile_case must save/restore
    /// ctx.scope for each branch or value_op.subscribe() will panic on the
    /// inner tmp VarRef.
    #[test]
    #[ignore = "if/else statement lowering not yet implemented (StmtKind::If unsupported)"]
    fn test_lower_if_else_branch_locals() {
        let code = "\
if cond:
    tmp = 1
    result = tmp + 1
else:
    tmp = 2
    result = tmp + 2
result";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &LoweringContext::default()).expect("lowering failed");
        // Fill in the expected string when StmtKind::If lowering is added.
        // Structure: let result = case cond of { True → let tmp = 1 in tmp + 1 | False → let tmp = 2 in tmp + 2 } in result
        assert_eq!(symbolic(&ccl), "");
    }

    /// Walrus operator `(y := expr)` lowers to `Expr::Let` in expression position,
    /// placing a Let directly in the value field of an outer Let:
    /// `let x = (let y = 5 in y) + 1 in x`.
    /// This is the only planned CHL construct that puts a Let directly in
    /// Let.value (not inside a Case branch). compile_let must be fixed to pass
    /// the post-value scope (not parent_scope) to value_op.subscribe() before
    /// this can run end-to-end.
    #[test]
    #[ignore = "walrus operator (:=) not yet implemented (ExprKind::NamedExpr unsupported)"]
    fn test_lower_walrus_let_in_value_position() {
        let code = "\
x = (y := 5) + 1
x";
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &LoweringContext::default()).expect("lowering failed");
        // Fill in the expected string when ExprKind::NamedExpr lowering is added.
        // Structure: let x = (let y = 5 in y) + 1 in x
        assert_eq!(symbolic(&ccl), "");
    }
}
